// Writeback Pipeline Stage
module wb_stage
import rv32imc_types::*;
(
  // Synchronous Signals
  input logic clk, rst,

  // Datapath Signals
  output logic        o_regf_we,
  output logic [4:0]  o_rd_addr,
  output logic [31:0] o_write_data,

  // Stall Signals
  input  logic wb_stall,
  output logic dmem_stall,

  // Data Memory Ports
  input  logic [31:0] dmem_rdata,
  input  logic [3:0]  dmem_rmask,
  input  logic [3:0]  dmem_wmask,
  input  logic        dmem_resp,

  // Pipeline Stage Registers
  input mem_stage_t mem_stage_reg,
  output wb_stage_t wb_stage_reg
);

logic mem_read, mem_write;
assign mem_read = mem_stage_reg.mem_ctrl.mem_read;
assign mem_write = mem_stage_reg.mem_ctrl.mem_write;

// Signal indicating if data memory is currently servicing a request
logic dmem_busy;
always_ff @(posedge clk) begin
  if (rst) begin
    dmem_busy <= 1'b0;
  end
  // We are busy if there is a current read from or write to data memory
  else if (|dmem_rmask || |dmem_wmask) begin
    dmem_busy <= 1'b1;
  end
  // We are not busy if there is a data memory response without a read or
  // write to data memory in the current cycle
  else if (dmem_resp) begin
    dmem_busy <= 1'b0;
  end
end

// Signal indicating to stall waiting for data memory response
assign dmem_stall = dmem_busy;  // For non-pipeline interface
// assign dmem_stall = dmem_busy & !dmem_resp; // For pipeline interface

// Data Memory Stall Logic
logic [31:0] dmem_rdata_buffer;
always_ff @(posedge clk) begin
  if (rst) begin
    dmem_rdata_buffer <= '0;
  end
  // If we are stalled, buffer the newest data from memory
  else if (wb_stall && mem_stage_reg.mem_ctrl.mem_read && dmem_resp) begin
    dmem_rdata_buffer <= dmem_rdata;
  end
end

logic [31:0] mem_rdata_raw;
assign mem_rdata_raw = dmem_resp ? dmem_rdata : dmem_rdata_buffer;

// Data Memory Logic
logic [31:0] mem_addr;
assign mem_addr = mem_stage_reg.func_out;

logic [31:0] mem_rdata;
always_comb begin
  // SEXT Logic
  unique case (mem_stage_reg.wb_ctrl.mem_funct3)
    lb : mem_rdata = {{24{mem_rdata_raw[7 +8 *mem_addr[1:0]]}}, mem_rdata_raw[8 *mem_addr[1:0] +: 8 ]};
    lbu: mem_rdata = {{24{1'b0}}                              , mem_rdata_raw[8 *mem_addr[1:0] +: 8 ]};
    lh : mem_rdata = {{16{mem_rdata_raw[15+16*mem_addr[1]  ]}}, mem_rdata_raw[16*mem_addr[1]   +: 16]};
    lhu: mem_rdata = {{16{1'b0}}                              , mem_rdata_raw[16*mem_addr[1]   +: 16]};
    lw : mem_rdata = mem_rdata_raw;
    default: mem_rdata = 'x;
  endcase
end

// Register file writeback logic
always_comb begin
  o_regf_we = mem_stage_reg.wb_ctrl.regf_we;
  o_rd_addr = mem_stage_reg.rd_addr;

  if (mem_stage_reg.wb_ctrl.wb_mux == func_out)
    o_write_data = mem_stage_reg.func_out;
  else
    o_write_data = mem_rdata;
end

// Latch to Pipeline Registers
always_ff @(posedge clk) begin
  if (rst) begin
    // Reset Pipeline Registers
    wb_stage_reg.rvfi <= '0;
  end else if (!wb_stall) begin
    // Latch Data Signals
    wb_stage_reg.rvfi.valid     <= mem_stage_reg.rvfi.valid;
    wb_stage_reg.rvfi.order     <= mem_stage_reg.rvfi.order;
    wb_stage_reg.rvfi.inst      <= mem_stage_reg.rvfi.inst;
    wb_stage_reg.rvfi.rs1_addr  <= mem_stage_reg.rvfi.rs1_addr;
    wb_stage_reg.rvfi.rs2_addr  <= mem_stage_reg.rvfi.rs2_addr;
    wb_stage_reg.rvfi.rs1_rdata <= mem_stage_reg.rvfi.rs1_rdata;
    wb_stage_reg.rvfi.rs2_rdata <= mem_stage_reg.rvfi.rs2_rdata;
    wb_stage_reg.rvfi.rd_addr   <= mem_stage_reg.rvfi.rd_addr;
    wb_stage_reg.rvfi.rd_wdata  <= o_write_data;
    wb_stage_reg.rvfi.pc_rdata  <= mem_stage_reg.rvfi.pc_rdata;
    wb_stage_reg.rvfi.pc_wdata  <= mem_stage_reg.rvfi.pc_wdata;
    wb_stage_reg.rvfi.mem_addr  <= mem_stage_reg.rvfi.mem_addr;
    wb_stage_reg.rvfi.mem_rmask <= mem_stage_reg.rvfi.mem_rmask;
    wb_stage_reg.rvfi.mem_wmask <= mem_stage_reg.rvfi.mem_wmask;
    wb_stage_reg.rvfi.mem_rdata <= mem_rdata_raw;
    wb_stage_reg.rvfi.mem_wdata <= mem_stage_reg.rvfi.mem_wdata;
  end
end

endmodule : wb_stage
