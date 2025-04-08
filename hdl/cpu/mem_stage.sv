// Data Memory Pipeline Stage
module mem_stage 
import rv32imc_types::*;
(
  // Synchronous Signals
  input logic clk, rst,

  // Stall Signals
  input  logic mem_stall,

  // Data Memory Ports
  output logic [31:0] dmem_addr,
  output logic [3:0]  dmem_rmask,
  output logic [3:0]  dmem_wmask,
  output logic [31:0] dmem_wdata,

  // Pipeline Stage Registers
  input  ex_stage_t  ex_stage_reg,
  output mem_stage_t mem_stage_reg
);

// Data Memory Logic
logic [31:0] mem_addr;
assign mem_addr = ex_stage_reg.func_out;
always_comb begin
  dmem_addr  = '0;
  dmem_rmask = '0;
  dmem_wmask = '0;
  dmem_wdata = '0;

  // Data Memory Read
  if (ex_stage_reg.mem_ctrl.mem_read) begin
    dmem_addr = {mem_addr[31:2], 2'b00};
    unique case(ex_stage_reg.mem_ctrl.mem_funct3)
      lb  : dmem_rmask = (!mem_stall) ? (4'h1 << mem_addr[1:0]) : '0;
      lbu : dmem_rmask = (!mem_stall) ? (4'h1 << mem_addr[1:0]) : '0;
      lh  : dmem_rmask = (!mem_stall) ? (4'h3 << mem_addr[1:0]) : '0;
      lhu : dmem_rmask = (!mem_stall) ? (4'h3 << mem_addr[1:0]) : '0;
      lw  : dmem_rmask = (!mem_stall) ? (4'hF)                  : '0;
      default: dmem_rmask = 'x;
    endcase
  end

  // Data Memory Write
  else if (ex_stage_reg.mem_ctrl.mem_write) begin
    dmem_addr = {mem_addr[31:2], 2'b00};
    unique case (ex_stage_reg.mem_ctrl.mem_funct3)
      sb : dmem_wmask = (!mem_stall) ? (4'h1 << mem_addr[1:0]) : '0;
      sh : dmem_wmask = (!mem_stall) ? (4'h3 << mem_addr[1:0]) : '0;
      sw : dmem_wmask = (!mem_stall) ? (4'hF)                  : '0;
      default: dmem_wmask = 'x;
    endcase
    unique case (ex_stage_reg.mem_ctrl.mem_funct3)
      sb : dmem_wdata[8 *mem_addr[1:0] +: 8 ] = ex_stage_reg.rs2_rdata[7:0];
      sh : dmem_wdata[16*mem_addr[1]   +: 16] = ex_stage_reg.rs2_rdata[15:0];
      sw : dmem_wdata = ex_stage_reg.rs2_rdata;
      default: dmem_wdata = 'x;
    endcase
  end
end

// RVFI Mask Logic
logic [3:0] rvfi_mem_rmask, rvfi_mem_wmask;
always_ff @(posedge clk, posedge rst) begin
  if (rst) begin
    rvfi_mem_rmask <= '0;
    rvfi_mem_wmask <= '0;
  end else if (mem_stall) begin
    rvfi_mem_rmask <= dmem_rmask;
    rvfi_mem_wmask <= dmem_wmask;
  end
end

// Latch to Pipeline Registers
always_ff @(posedge clk, posedge rst) begin
  if (rst) begin
    // Reset Pipeline Registers
    mem_stage_reg.rd_addr    <= '0;
    mem_stage_reg.func_out   <= '0;
    mem_stage_reg.mem_ctrl   <= '0;
    mem_stage_reg.wb_ctrl    <= '0;
    mem_stage_reg.rvfi       <= '0;
  end else if (!mem_stall) begin
    // Latch Data Signals
    mem_stage_reg.rd_addr  <= ex_stage_reg.rd_addr;
    mem_stage_reg.func_out <= ex_stage_reg.func_out;
    
    // Latch Control Signals
    mem_stage_reg.mem_ctrl <= ex_stage_reg.mem_ctrl;
    mem_stage_reg.wb_ctrl  <= ex_stage_reg.wb_ctrl;
    mem_stage_reg.int_flag <= ex_stage_reg.int_flag;

    // Latch RVFI Signals
    mem_stage_reg.rvfi            <= '0;
    mem_stage_reg.rvfi.valid      <= ex_stage_reg.rvfi.valid;
    mem_stage_reg.rvfi.order      <= ex_stage_reg.rvfi.order;
    mem_stage_reg.rvfi.int_valid  <= ex_stage_reg.rvfi.int_valid;
    mem_stage_reg.rvfi.end_signal <= ex_stage_reg.rvfi.end_signal;
    
    mem_stage_reg.rvfi.int_order <= ex_stage_reg.rvfi.int_order;
    mem_stage_reg.rvfi.inst      <= ex_stage_reg.rvfi.inst;
    mem_stage_reg.rvfi.rs1_addr  <= ex_stage_reg.rvfi.rs1_addr;
    mem_stage_reg.rvfi.rs2_addr  <= ex_stage_reg.rvfi.rs2_addr;
    mem_stage_reg.rvfi.rs1_rdata <= ex_stage_reg.rvfi.rs1_rdata;
    mem_stage_reg.rvfi.rs2_rdata <= ex_stage_reg.rvfi.rs2_rdata;
    mem_stage_reg.rvfi.rd_addr   <= ex_stage_reg.rvfi.rd_addr;
    mem_stage_reg.rvfi.pc_rdata  <= ex_stage_reg.rvfi.pc_rdata;
    mem_stage_reg.rvfi.pc_wdata  <= ex_stage_reg.rvfi.pc_wdata;
    mem_stage_reg.rvfi.mem_addr  <= dmem_addr;
    mem_stage_reg.rvfi.mem_rmask <= (!mem_stall) ? dmem_rmask : rvfi_mem_rmask;
    mem_stage_reg.rvfi.mem_wmask <= (!mem_stall) ? dmem_wmask : rvfi_mem_wmask;
    mem_stage_reg.rvfi.mem_wdata <= dmem_wdata;
  end
end

endmodule : mem_stage
