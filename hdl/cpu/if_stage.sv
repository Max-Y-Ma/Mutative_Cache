// Instruction Fetch Pipeline Stage
module if_stage
import rv32imc_types::*;
(
  // Synchronous Signals
  input  logic clk, rst,

  // Control/Datapath Signals
  input  pc_mux_t     i_pc_mux,
  input  logic [31:0] i_pc_offset,

  // Flush Signals
  input  logic i_flush,

  // Stall Signals
  input  logic if_stall,

  // Instruction Memory Ports
  output logic [31:0] imem_addr,
  output logic [3:0]  imem_rmask,

  // Pipeline Stage Registers
  output if_stage_t if_stage_reg
);

// Program Counter
logic [31:0] pc;
logic [31:0] pc_next;
always_ff @(posedge clk) begin
  // Set program counter to reset vector upon a reset
  if (rst) begin
    pc <= 32'h60000000;
  end
  // During a flush cycle, the target address will be read from memory. So the
  // program counter should be set to the next instruction from the target
  // address
  else if (i_flush && !if_stall) begin
    pc <= pc_next + 'd4;
  end
  // Otherwise, we can set program counter to next state
  else if (!if_stall) begin
    pc <= pc_next;
  end
end

// Program Counter Logic
assign pc_next = (i_pc_mux == pc_offset) ? (i_pc_offset) : (pc + 'd4);

// Assign instruction memory address to the branch target address during a
// flush cycle in which a branch was taken, otherwise just the current pc.
assign imem_addr = i_flush ? pc_next : pc;

// Assert read mask unless we are stalled
assign imem_rmask = (!if_stall) ? 4'hF : 4'b0;

// Latch to Pipeline Registers
always_ff @(posedge clk) begin
  if (rst) begin
    // Reset Pipeline Registers
    if_stage_reg.pc      <= '0;
    if_stage_reg.pc_next <= '0;
    if_stage_reg.rvfi    <= '0;
  end else if (!if_stall) begin
    // Latch Program Counters
    if_stage_reg.pc      <= imem_addr;
    if_stage_reg.pc_next <= imem_addr + 'd4;

    // Latch RVFI Signals
    if_stage_reg.rvfi.valid    <= 1'b1;
    if_stage_reg.rvfi.pc_rdata <= imem_addr;
    if_stage_reg.rvfi.pc_wdata <= imem_addr + 'd4;
  end
end

endmodule : if_stage
