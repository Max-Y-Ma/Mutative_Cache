import "DPI-C" function string getenv(input string env_name);

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
int clock_half_period_ps = getenv("ECE411_CLOCK_PERIOD_PS").atoi() / 2;

bit clk;
always #(clock_half_period_ps) clk = ~clk;

bit rst;

// Memory Interface
banked_mem_itf bmem_itf(.*);

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
  banked_memory mem(.itf(bmem_itf));
  // random_banked_memory random_banked_memory(.itf(bmem_itf));
`endif

// DUT Instantiation
core dut(
  .clk            (clk),
  .rst            (rst),

  .bmem_addr      (bmem_itf.addr),
  .bmem_read      (bmem_itf.read),
  .bmem_write     (bmem_itf.write),
  .bmem_wdata     (bmem_itf.wdata),
  .bmem_ready     (bmem_itf.ready),

  .bmem_raddr     (bmem_itf.raddr),
  .bmem_rdata     (bmem_itf.rdata),
  .bmem_rvalid    (bmem_itf.rvalid)
);

// Monitor Interface DUT Wiring
`include "../../hvl/vc/core/rvfi_reference.svh"

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
    $display("hit rate: %0f", real'(dut.mutative_cache0.setup_control.hit_counter)/real'(dut.mutative_cache0.setup_control.request_counter));
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
  if (bmem_itf.error != 0) begin
      repeat (5) @(posedge clk);
      $finish;
  end
  timeout_cycles <= timeout_cycles - 1;
end

endmodule : top_tb
