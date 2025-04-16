// Execute Pipeline Stage
module ex_stage
import rv32imc_types::*;
(
  // Synchronous Signals
  input logic clk, rst,

  // Datapath Signals
  output pc_mux_t     o_pc_mux,
  output logic [31:0] o_pc_offset,

  // Stall Signals
  input  logic ex_stall,
  input  logic dmem_stall,
  output logic func_stall,

  // Flush Signals
  output logic o_flush,

  // Writeback Signal
  input logic [31:0] i_wb_data,

  // Pipeline Stage Registers
  input  id_stage_t  id_stage_reg,
  input  mem_stage_t mem_stage_reg,
  output ex_stage_t  ex_stage_reg
);

// Forwarding Unit
forward_mux_t fwd_src_a;
forward_mux_t fwd_src_b;
forwarding_unit forwarding_unit0 (
  .rs1_addr    (id_stage_reg.rs1_addr),
  .rs2_addr    (id_stage_reg.rs2_addr),
  .ex_rd_addr  (ex_stage_reg.rd_addr),
  .mem_rd_addr (mem_stage_reg.rd_addr),
  .ex_regf_we  (ex_stage_reg.wb_ctrl.regf_we),
  .mem_regf_we (mem_stage_reg.wb_ctrl.regf_we),
  .fwd_src_a   (fwd_src_a),
  .fwd_src_b   (fwd_src_b)
);

// Source Operands
logic [31:0] a, b;
logic [31:0] fwd_src_a_data, fwd_src_b_data;
always_comb begin
  // Default Values
  a = '0; fwd_src_a_data = '0;
  b = '0; fwd_src_b_data = '0;

  // Assign RS1 data based on forwarding unit
  if (fwd_src_a == ex_source) begin
    fwd_src_a_data = ex_stage_reg.func_out;
  end
  else if (fwd_src_a == mem_source) begin
    fwd_src_a_data = i_wb_data;
  end
  else begin
    fwd_src_a_data = id_stage_reg.rs1_rdata;
  end

  // Assign RS2 data based on forwarding unit
  if (fwd_src_b == ex_source) begin
    fwd_src_b_data = ex_stage_reg.func_out;
  end
  else if (fwd_src_b == mem_source) begin
    fwd_src_b_data = i_wb_data;
  end
  else begin
    fwd_src_b_data = id_stage_reg.rs2_rdata;
  end

  // Operand multiplexers
  if (id_stage_reg.ex_ctrl.alu1_mux == pc_out) begin
    a = id_stage_reg.pc;
  end
  else begin
    a = fwd_src_a_data;
  end

  if (id_stage_reg.ex_ctrl.alu2_mux == imm_out) begin
    b = id_stage_reg.imm;
  end
  else begin
    b = fwd_src_b_data;
  end
end

// Memory forward conditions
logic mem_forward;
assign mem_forward = (fwd_src_a == mem_source) | (fwd_src_b == mem_source);

// Arithmetic Logic Unit
logic [31:0] alu_fout;
alu alu0 (
  .a        (a),
  .b        (b),
  .alu_op   (id_stage_reg.ex_ctrl.func_op),
  .alu_fout (alu_fout)
);

// Multiplier
logic mul_stall;
logic [31:0] mul_fout;

// Current operation is a multiplication
logic multiply;
assign multiply = (id_stage_reg.ex_ctrl.func_mux == mul_out);

// Activate a multiply operation during a multiplication instruction.
// If there is a forward condition from memory wait until dmem_response.
logic mul_activate;
assign mul_activate = (multiply && !mem_forward) || (multiply && !dmem_stall);

// Pulse the multiply start signal for the operation to begin
logic mul_start;
logic mul_start_strobe;
always_ff @(posedge clk) begin
  if (rst || !ex_stall) begin
    mul_start <= 1'b0;
  end
  else if (mul_activate) begin
    mul_start <= 1'b1;
  end
end

// Strobe is a pulse that is high for one cycle indicating the start of a
// multiplication operation.
assign mul_start_strobe = mul_activate & ~mul_start;

multiplier multiplier0 (
  .clk(clk),
  .rst(rst),
  .a(a),
  .b(b),
  .start(mul_start_strobe),
  .mul_op(id_stage_reg.ex_ctrl.func_op),
  .mul_funct3(id_stage_reg.ex_ctrl.funct3),
  .mul_fout(mul_fout),
  .mul_stall(mul_stall)
);

// Divider
logic div_stall;
logic divide_by_0;
logic [31:0] div_fout;

// Current operation is a division
logic divide;
assign divide = (id_stage_reg.ex_ctrl.func_mux == div_out);

// Activate a multiply operation during a multiplication instruction.
// If there is a forward condition from memory wait until dmem_response.
logic div_activate;
assign div_activate = (divide && !mem_forward) || (divide && !dmem_stall);

// Pulse the divide start signal
logic div_start;
logic div_start_strobe;
always_ff @(posedge clk) begin
  if (rst || !ex_stall) begin
    div_start <= 1'b0;
  end
  else if (div_activate) begin
    div_start <= 1'b1;
  end
end

// Strobe is a pulse that is high for one cycle indicating the start of a
// division operation.
assign div_start_strobe = divide & ~div_start;

divider divider0 (
  .clk(clk),
  .rst(rst),
  .a(a),
  .b(b),
  .start(div_start_strobe),
  .div_op(id_stage_reg.ex_ctrl.func_op),
  .div_fout(div_fout),
  .div_stall(div_stall),
  .divide_by_0(divide_by_0)
);

// Comparator
logic br_en;
cmp cmp0 (
  .a (a),
  .b (b),
  .cmp_op (id_stage_reg.ex_ctrl.func_op),
  .br_en (br_en)
);

// Functional stall logic
// Wait for data memory if we are forwarding from memory during a divide
// or multiply operation
logic wait_stall;
assign wait_stall = (multiply | divide) & mem_forward & dmem_stall;

assign func_stall = mul_stall | div_stall | wait_stall;

// ALU Output Logic
logic [31:0] func_out;
always_comb begin
  if (id_stage_reg.ex_ctrl.func_mux == alu_out) begin
    func_out = alu_fout;
  end
  else if (id_stage_reg.ex_ctrl.func_mux == cmp_out) begin
    func_out = {31'd0, br_en};
  end
  else if (id_stage_reg.ex_ctrl.func_mux == addr_out) begin
    func_out = id_stage_reg.pc + 'h4;
  end
  else if (id_stage_reg.ex_ctrl.func_mux == mul_out) begin
    func_out = mul_fout;
  end
  else begin
    func_out = div_fout;
  end
end

// Branch Logic
logic  branch_taken;
assign branch_taken = id_stage_reg.ex_ctrl.branch & br_en;

logic [31:0] base_addr, target_addr, pc_imm;
always_comb begin
  // Determine base address value for branches or jumps
  if (id_stage_reg.ex_ctrl.target_addr_mux == rs1_op)
    base_addr = fwd_src_a_data;
  else
    base_addr = id_stage_reg.pc;

  // Add the immediate offset to the base address to form the target address
  target_addr = base_addr + id_stage_reg.imm;

  // Assert the next program counter value in fetch stage
  o_pc_mux = branch_taken ? pc_offset : pc_next;

  if (id_stage_reg.ex_ctrl.target_addr_mux == rs1_op)
    o_pc_offset = target_addr & 32'hfffffffe;
  else
    o_pc_offset = target_addr;
end

// Branch Flush Logic
assign o_flush = branch_taken;

// Latch to Pipeline Registers
always_ff @(posedge clk) begin
  if (rst) begin
    // Reset Pipeline Registers
    ex_stage_reg.func_out  <= '0;
    ex_stage_reg.rs2_rdata <= '0;
    ex_stage_reg.rd_addr   <= '0;
    ex_stage_reg.mem_ctrl  <= '0;
    ex_stage_reg.wb_ctrl   <= '0;
    ex_stage_reg.rvfi      <= '0;
  end else if (!ex_stall) begin
    // Latch Data Signals
    ex_stage_reg.func_out  <= func_out;
    ex_stage_reg.rs2_rdata <= fwd_src_b_data;
    ex_stage_reg.rd_addr   <= id_stage_reg.rd_addr;

    // Latch Control Signals
    ex_stage_reg.mem_ctrl <= id_stage_reg.mem_ctrl;
    ex_stage_reg.wb_ctrl  <= id_stage_reg.wb_ctrl;

    // Latch RVFI Signals
    ex_stage_reg.rvfi.valid     <= id_stage_reg.rvfi.valid;
    ex_stage_reg.rvfi.order     <= id_stage_reg.rvfi.order;
    ex_stage_reg.rvfi.inst      <= id_stage_reg.rvfi.inst;
    ex_stage_reg.rvfi.rs1_addr  <= id_stage_reg.rvfi.rs1_addr;
    ex_stage_reg.rvfi.rs2_addr  <= id_stage_reg.rvfi.rs2_addr;
    ex_stage_reg.rvfi.rs1_rdata <= fwd_src_a_data;
    ex_stage_reg.rvfi.rs2_rdata <= fwd_src_b_data;
    ex_stage_reg.rvfi.rd_addr   <= id_stage_reg.rvfi.rd_addr;
    ex_stage_reg.rvfi.pc_rdata  <= id_stage_reg.rvfi.pc_rdata;
    ex_stage_reg.rvfi.pc_wdata  <= branch_taken ? o_pc_offset : id_stage_reg.rvfi.pc_wdata;
  end
end

endmodule : ex_stage
