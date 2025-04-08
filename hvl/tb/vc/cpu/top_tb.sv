`ifdef RANDOM
  `include "cpu_pkg.svh"
`endif

module top_tb;

timeunit 1ps;
timeprecision 1ps;

// UVM Imports
`ifdef RANDOM
  import uvm_pkg::*;
  `include "uvm_macros.svh"
`endif

// Clock Generation
`define CLK_HALF_PERIOD (5)
bit clk;
always #(`CLK_HALF_PERIOD) clk = ~clk;

bit rst;

// Memory Interface
mem_itf mem_itf_i(.clk(clk), .rst(rst));
mem_itf mem_itf_d(.clk(clk), .rst(rst));

// Monitor Interface
mon_itf mon_itf(.*);    
monitor monitor(.itf(mon_itf));

// Test Suite
`ifdef RANDOM
  initial begin
    // UVM Constrained Random Tests
    uvm_config_db #(virtual mem_itf)::set(null, "*", "mem_itf_i", mem_itf_i);
    uvm_config_db #(virtual mem_itf)::set(null, "*", "mem_itf_d", mem_itf_d);
    run_test();
  end
`else
  // Memory Types for Directed Test
  // magic_dual_port mem(.itf_i(mem_itf_i), .itf_d(mem_itf_d));
  ordinary_dual_port mem(.itf_i(mem_itf_i), .itf_d(mem_itf_d));
`endif


  logic [4:0]  adp_rd_addr;
  logic [31:0] adp_wdata;
  logic        adp_reg_we;
  logic        adp_pc_we;
  logic        adp_ir_we;
  logic        adp_ctrl_stall;

  assign adp_ctrl_stall  = '0;
  assign adp_rd_addr     = '0;
  assign adp_wdata       = '0;
  assign adp_pc_we       = '0;  
  assign adp_ir_we       = '0;

// DUT Instantiation
cpu dut(
  .clk            (clk),
  .rst            (rst),

  // Instruction Memory Port
  .imem_addr      (mem_itf_i.addr),
  .imem_rmask     (mem_itf_i.rmask),
  .imem_rdata     (mem_itf_i.rdata),
  .imem_resp      (mem_itf_i.resp),

  // Data Memory Port
  .dmem_addr      (mem_itf_d.addr),
  .dmem_rmask     (mem_itf_d.rmask),
  .dmem_wmask     (mem_itf_d.wmask),
  .dmem_rdata     (mem_itf_d.rdata),
  .dmem_wdata     (mem_itf_d.wdata),
  .dmem_resp      (mem_itf_d.resp),

    // ADP debug signal interface
  .adp_core_reg(),
  .adp_core_pc(),
  .adp_core_ir(),
  .adp_rd_addr(adp_rd_addr),
  .adp_wdata(adp_wdata),
  .adp_reg_we(),
  .adp_pc_we(adp_pc_we),
  .adp_ir_we(adp_ir_we),
  .adp_imem_stall(adp_imem_stall),
  .adp_dmem_stall(adp_dmem_stall),
  .adp_func_stall(adp_func_stall),
  .adp_load_hazard(adp_load_hazard),
  .adp_ctrl_stall(adp_ctrl_stall)
);


// Monitor Interface DUT Wiring
`include "../../chip/tb/vc/cpu/rvfi_reference.svh"

// Waveform Dumpfiles and Reset
initial begin
  $fsdbDumpfile("dump.fsdb");
  $fsdbDumpvars(0, "+all");
  rst = 1'b1;
  repeat (2) @(posedge clk);
  rst <= 1'b0;
end

// End Condition
int timeout_cycles = 10000000;
always @(posedge clk) begin
  if (mon_itf.halt) begin
    $finish;
  end
  if (timeout_cycles == 0) begin
    $error("TB Error: Timed out");
    $finish;
  end
  if (mon_itf.error != 0) begin
    repeat (5) @(posedge clk);
    $finish;
  end
  if (mem_itf_i.error != 0) begin
    repeat (5) @(posedge clk);
    $finish;
  end
  if (mem_itf_d.error != 0) begin
    repeat (5) @(posedge clk);
    $finish;
  end
  timeout_cycles <= timeout_cycles - 1;
end

endmodule : top_tb