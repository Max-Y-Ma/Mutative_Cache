// Instruction Fetch Pipeline Stage
module if_stage 
import rv32imc_types::*;
(
  // Synchronous Signals
  input  logic        clk, 
  input  logic        rst,

  // Interrupt Signals
  input  logic         i_signaled_int,
  input  logic         i_end_int,
  input  logic [31:0]  i_int_PC,
  output logic         o_int_accepted,
  // Control/Datapath Signals
  input  logic        i_compressed,
  input  logic        i_compr_int,
  // output logic        o_compressed_flush,
  input  pc_mux_t     i_pc_mux,
  input  logic [31:0] i_pc_offset,

  // Flush Signals
  input  logic        i_branch_flush,
  input  logic        i_branch_int,

  // Stall Signals
  input  logic        if_stall,

  // Instruction Memory Ports
  // input  logic        imem_resp,
  output logic [31:0] imem_addr,
  output logic [3:0]  imem_rmask,

  // Pipeline Stage Registers
  output if_stage_t   if_stage_reg,

  // ADP Debug Signals
  input  logic [31:0] adp_wdata,
  input  logic        adp_pc_we,
  output logic [31:0] adp_core_pc
);

// Program Counter
logic [31:0] pc;
logic [31:0] pc_next;
logic [31:0] saved_pc; //pc to save when interrupted
logic        latch_int_start, start_int;
logic        int_instr; //logic to denote wether this instr is part of int handler

//start int if we are no longer stalling and we are not in progress of ending one
assign start_int      = (latch_int_start && ~if_stall && ~i_end_int); 

//signal back to interrupt_controller that we started the interrupt
assign o_int_accepted = start_int;

always_ff @(posedge clk, posedge rst) begin
  // Set program counter to reset vector upon a reset
  if (rst) begin
    pc              <= 32'h60000000;
    saved_pc        <= 32'h00000000;
    latch_int_start <= 1'b0;
    int_instr       <= 1'b0;
  end else begin
    if(i_signaled_int) begin  //detect when a new interrupt has come in and store it 
      latch_int_start <= 1'b1; 
    end 

    if(i_end_int) begin //when mret signaled, then lower int_flag
      int_instr <= 1'b0;
    end

    //if our interrupt has been signaled, then save the last excuted PC,
    //and set the new PC to the current i_int_PC
    unique case(start_int)
      default: begin
        //if we are servicing an int handler but get a branch from previous instr
        //then update the saved_pc to the new offset
        if (i_branch_flush && ~i_branch_int && int_instr && ~if_stall) begin 
          saved_pc <= i_pc_offset;
        end

        //if we are servicing an interrupt, and recieve a compressed signal
        //from a previous isntr. then update by substracing two
        if (i_compressed && ~i_compr_int && int_instr && ~if_stall) begin 
          saved_pc <= saved_pc - 'd2;
        end

        if (adp_pc_we) begin
          pc <= adp_wdata;
        end else if(~if_stall && i_end_int) begin
        // During a flush cycle, the target address will be read from memory. So the
        // pc should be set to the next instruction from the target address.
          pc <= saved_pc +'d4;
        end else if (i_branch_flush && ~if_stall && (i_branch_int ~^ int_instr)) begin
          pc <= pc_next + 'd4; // Static Not-Compressed 
        end 
        // Otherwise, we can set program counter to next state
        else if (~if_stall) begin
          pc <= pc_next;
        end 

      end
      1: begin //once we start int (we already stopped stalling)
       
        //if branch and int handled at same time, then pc_next is already sent down pipeline
        //update saved_pc with the next_pc
        if (i_branch_flush && (i_branch_int ~^ int_instr)) begin
          saved_pc <= pc_next + 'd4;
        end else begin
          saved_pc <= pc_next; //save the next pc and switch to interrupt handler
        end

        pc       <= i_int_PC;

        latch_int_start <= 1'b0; //once interrupt starts then clear register
        int_instr       <= 1'b1; //instr_flag to denote part of int handlere
      end
    endcase

  end
end

// ADP Debug Signals
assign adp_core_pc = pc;

// Branching takes the most priority since later instructions are speculative.
// Otherwise, we increment by two if the previous instruction was compressed.
// Else, we increment by four for a normal instruction.
always_comb begin
  //given a branch predict/jalr only update if we are servicing an int and this flush came from an interrupt isntr
  //or if we are in normal execution flow and the flush is from a non-interupt instr.
  if (i_pc_mux == pc_offset && (i_branch_int ~^ int_instr)) begin 
    pc_next = i_pc_offset;
  end
  else if (i_compressed && (i_compr_int ~^ int_instr)) begin
    pc_next = pc + 'd2;
  end 
  else begin
    pc_next = pc + 'd4; 
  end 
end

always_comb begin
  // Assign instruction memory address to the branch target address during a 
  // branch flush cycle in which a branch was taken.
  // if an interupt is started, then pc_next is appropriately saved?
  if (i_branch_flush && (i_branch_int ~^ int_instr)) begin
    imem_addr = pc_next;
  end else if(i_end_int) begin //if our interrupt ends, send a request of our saved pc
    imem_addr = saved_pc;
  end
  else if (i_compressed && (i_compr_int ~^ int_instr)) begin
    imem_addr = pc - 'd2;
  end
  else begin
    imem_addr = pc;
  end
end
 
// Assert read mask unless we are stalled or ending an interrupt
assign imem_rmask = (!if_stall) ? 4'hF : 4'b0;

// Latch to Pipeline Registers
always_ff @(posedge clk, posedge rst) begin
  if (rst) begin
    // Reset Pipeline Registers
    if_stage_reg.pc       <= '0;
    if_stage_reg.pc_next  <= '0;
    if_stage_reg.rvfi     <= '0;
    if_stage_reg.int_flag <= '0;
  end else if (!if_stall) begin
    // Latch Program Counters
    if_stage_reg.pc      <= imem_addr;
    if_stage_reg.pc_next <= imem_addr + 'd4;

    // Interrupt Flag Signal
    //we are an interrupt instruction when this flag is high and 
    //the interrupt signal has not been set to end
    if_stage_reg.int_flag <= int_instr && ~i_end_int;

    // Latch RVFI Signals
    if_stage_reg.rvfi          <= '0;
    if_stage_reg.rvfi.valid      <= ~int_instr || i_end_int;
    if_stage_reg.rvfi.end_signal <= i_end_int && ~if_stall;
    if_stage_reg.rvfi.int_valid  <= int_instr && ~i_end_int;
    if_stage_reg.rvfi.pc_rdata   <= imem_addr;
    if_stage_reg.rvfi.pc_wdata   <= imem_addr + 'd4;
  end
end



endmodule : if_stage
