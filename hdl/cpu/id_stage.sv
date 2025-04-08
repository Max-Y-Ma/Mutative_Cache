// Instruction Decode Pipeline Stage
module id_stage 
import rv32imc_types::*;
(
  // Synchronous Signals
  input  logic clk, rst,

  // Control/Datapath Signals
  output logic        o_compressed,
  output logic        o_compr_int_flag,
  input  logic        i_regf_we,
  input  logic [4:0]  i_rd_addr,
  input  logic [31:0] i_rd_wdata,

  // Flush Signals
  input  logic i_branch_flush,
  input  logic i_branch_int,
  // input  logic i_compressed_flush,

  // Stall Signals
  input  logic id_stall,
  input  logic ex_stall,
  output logic imem_stall,
  output logic load_hazard,

  // Instruction Memory Ports
  input  logic [3:0]  imem_rmask,
  input  logic [31:0] imem_rdata,
  input  logic        imem_resp,

  //Interrupt Start/End Signals
  input logic i_start_interrupt,
  input logic i_end_interrupt,
  input logic i_wb_int_flag,

  // Pipeline Stage Registers
  input  if_stage_t if_stage_reg,
  output id_stage_t id_stage_reg,

  // ADP Debug Signals
  input  logic [4:0]  adp_rd_addr,
  input  logic [31:0] adp_wdata,
  input  logic        adp_reg_we,
  input  logic        adp_ir_we,
  output logic [31:0] adp_core_ir,
  output logic [31:0] adp_core_reg [32]
);

// Decode flush signals
logic  id_flush;
//flush iff the flush corresponds to the same instr type
assign id_flush = i_branch_flush && (i_branch_int ~^ if_stage_reg.int_flag); 
assign o_compr_int_flag = if_stage_reg.int_flag;

// Signal indicating if instruction memory is currently servicing a request
logic imem_busy;
always_ff @(posedge clk, posedge rst) begin
  // We are not busy if there is a instruction memory response but we are
  // still stalled because of other conditions
  if (rst) begin
    imem_busy <= 1'b0;
  end 
  else if ((imem_resp & (id_stall || load_hazard))) begin
    imem_busy <= 1'b0;
  end
  // We are busy if there is a current read from instruction memory or a 
  // instruction memory response comes, in which we read again immediately
  else if (|imem_rmask || imem_resp) begin
    imem_busy <= 1'b1;
  end
end

// Signal indicating to stall waiting for instruction memory response
assign imem_stall = imem_busy & !imem_resp;

// Instruction Stall Logic
logic [31:0] inst_raw, inst, inst_buffer;
always_ff @(posedge clk, posedge rst) begin
  // If we get flushed, reset the instruction buffer
  if (rst) begin
    inst_buffer <= 'h13;
  end 
  // Support ADP Debug writes
  else if (adp_ir_we) begin
    inst_buffer <= adp_wdata;
  end
  // If we are stalled, buffer the newest instruction data from memory
  else if ((id_stall || load_hazard) && imem_resp) begin
    inst_buffer <= imem_rdata;
  end
end 

// Current instruction logic
always_comb begin
  // During a flush cycle, we should process a NOP instruction
  if (id_flush) begin
    inst_raw = 'h13;
  end
  // Otherwise, the current instruction could be from memory, ADP, or
  // it could have been latched from a stall condition
  else begin
    inst_raw = imem_resp ? imem_rdata : inst_buffer;
  end
end

// ADP Debug Signals
assign adp_core_ir = inst_buffer;

// Converts a 16-bit instruction to 32-bit normal instruction
logic illegal;
compressed_decoder compressed_decoder0 (
  .i_instr(inst_raw),
  .o_instr(inst),
  .o_compressed(o_compressed),
  .o_illegal(illegal)
);

// Control Unit
logic [4:0]   rs1_addr, rs2_addr, rd_addr;
logic [31:0]  imm;
ex_ctrl_t     ex_ctrl;
mem_ctrl_t    mem_ctrl;
wb_ctrl_t     wb_ctrl;
decoder decoder0 (
  .inst(inst),
  .o_rs1_addr(rs1_addr),
  .o_rs2_addr(rs2_addr),
  .o_rd_addr(rd_addr),
  .o_imm(imm),
  .ex_ctrl(ex_ctrl),
  .mem_ctrl(mem_ctrl),
  .wb_ctrl(wb_ctrl)
);

// Register File
logic [31:0] rs1_rdata, rs2_rdata;
regfile #(
  .NUM_REGS(32)
) regfile0 (
  .clk(clk),
  .rst(rst),
  .regf_we(i_regf_we),
  .rd_wdata(i_rd_wdata),
  .rd_addr(i_rd_addr),
  .rs1_addr(rs1_addr),
  .rs2_addr(rs2_addr),
  .rs1_rdata(rs1_rdata),
  .rs2_rdata(rs2_rdata),
  .adp_rd_addr(adp_rd_addr),
  .adp_wdata(adp_wdata),
  .adp_reg_we(adp_reg_we),
  .adp_core_reg(adp_core_reg),
  .start_interrupt(i_start_interrupt),
  .end_interrupt(i_end_interrupt),
  .int_instr(if_stage_reg.int_flag),
  .wb_int_flag(i_wb_int_flag)
);

// Hazard Detection Unit
detection_unit detection_unit0 (
  .ex_mem_read(id_stage_reg.mem_ctrl.mem_read), // Current execute stage signal
  .ex_rd_addr(id_stage_reg.rd_addr),            // Current execute stage signal
  .rs1_addr(rs1_addr),
  .rs2_addr(rs2_addr),
  .load_hazard(load_hazard)
);

// RVFI Order Logic
logic [63:0] order;
logic [63:0] int_order;
always_ff @(posedge clk, posedge rst) begin
  if (rst) begin
    order     <= '0;
    int_order <= '0;
  end 
  // Order unchanged if a flush or stall cycle
  else begin
    if (id_stall || load_hazard || id_flush) begin
      int_order <= int_order;
    end
    else if (if_stage_reg.rvfi.valid) begin
      order     <= order + 1'b1;
    end

    if(i_end_interrupt) begin
      int_order <= '0;
    end else if (id_stall || load_hazard || id_flush) begin
      int_order <= int_order;
    end else if(if_stage_reg.rvfi.int_valid) begin
      int_order <= int_order + 1'b1;
    end
  end

end

// Latch to Pipeline Registers
always_ff @(posedge clk, posedge rst) begin
  // During a load hazard or flush, pass a bubble on the next available cycle
  if (rst) begin
    id_stage_reg.pc         <= '0;
    id_stage_reg.pc_next    <= '0;
    id_stage_reg.rs1_addr   <= '0;
    id_stage_reg.rs2_addr   <= '0;
    id_stage_reg.rd_addr    <= '0;
    id_stage_reg.imm        <= '0;
    id_stage_reg.rs1_rdata  <= '0;
    id_stage_reg.rs2_rdata  <= '0;
    id_stage_reg.ex_ctrl    <= '0;
    id_stage_reg.mem_ctrl   <= '0;
    id_stage_reg.wb_ctrl    <= '0;
    id_stage_reg.int_flag   <= '0;
    id_stage_reg.rvfi       <= '0;
  end 
  else if (((load_hazard || id_flush) && !ex_stall)) begin
    id_stage_reg.pc         <= '0;
    id_stage_reg.pc_next    <= '0;
    id_stage_reg.rs1_addr   <= '0;
    id_stage_reg.rs2_addr   <= '0;
    id_stage_reg.rd_addr    <= '0;
    id_stage_reg.imm        <= '0;
    id_stage_reg.rs1_rdata  <= '0;
    id_stage_reg.rs2_rdata  <= '0;
    id_stage_reg.ex_ctrl    <= '0;
    id_stage_reg.mem_ctrl   <= '0;
    id_stage_reg.wb_ctrl    <= '0;
    id_stage_reg.int_flag   <= '0;
    id_stage_reg.rvfi       <= '0;
    id_stage_reg.int_flag   <= '0;
  end
  else if (!id_stall) begin
    // Latch Program Counters
    id_stage_reg.pc      <= if_stage_reg.pc;
    id_stage_reg.pc_next <= o_compressed ?
                            if_stage_reg.pc_next - 'd2 :
                            if_stage_reg.pc_next;

    // Latch Immediate Value
    id_stage_reg.imm <= imm;

    // Latch Register File Data
    id_stage_reg.rs1_addr  <= rs1_addr;
    id_stage_reg.rs2_addr  <= rs2_addr;
    id_stage_reg.rd_addr   <= rd_addr;
    id_stage_reg.rs1_rdata <= rs1_rdata;
    id_stage_reg.rs2_rdata <= rs2_rdata;

    // Latch Control Signals
    id_stage_reg.ex_ctrl  <= ex_ctrl;
    id_stage_reg.mem_ctrl <= mem_ctrl;
    id_stage_reg.wb_ctrl  <= wb_ctrl;

    //Interrupt Flag Signal
    id_stage_reg.int_flag <= if_stage_reg.int_flag;

    // Latch RVFI Signals
    // id_stage_reg.rvfi            <= '0;
    id_stage_reg.rvfi.valid      <= if_stage_reg.rvfi.valid;
    id_stage_reg.rvfi.int_valid  <= if_stage_reg.rvfi.int_valid;
    id_stage_reg.rvfi.order      <= order;
    id_stage_reg.rvfi.int_order  <= int_order;
    id_stage_reg.rvfi.end_signal <= if_stage_reg.rvfi.end_signal;
    id_stage_reg.rvfi.inst       <= inst_raw;
    id_stage_reg.rvfi.rs1_addr   <= rs1_addr;
    id_stage_reg.rvfi.rs2_addr   <= rs2_addr;
    id_stage_reg.rvfi.rs1_rdata  <= rs1_rdata;
    id_stage_reg.rvfi.rs2_rdata  <= rs2_rdata;
    id_stage_reg.rvfi.rd_addr    <= rd_addr;
    id_stage_reg.rvfi.pc_rdata   <= if_stage_reg.rvfi.pc_rdata;
    id_stage_reg.rvfi.pc_wdata   <= o_compressed ? 
                                   if_stage_reg.rvfi.pc_wdata - 'd2 : 
                                   if_stage_reg.rvfi.pc_wdata;
  end
end

endmodule : id_stage
