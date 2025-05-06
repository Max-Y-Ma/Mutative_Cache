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

import cache_types::*;

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

int csb_zero_cycles[8] = {0, 0, 0, 0, 0, 0, 0, 0};
int csb_level_changes_cycles[8] = {0, 0, 0, 0, 0, 0, 0, 0};
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
int hit_counter = 0;
int request_counter = 0;
always @(posedge clk) begin
  if (mon_itf.halt) begin
    $display("hit rate: %0f", real'(hit_counter)/real'(request_counter));
    for(int i = 0; i < 8; i++) begin
      $display("way [%0d] csb level changes (1 -> 0): %0d", i, csb_level_changes_cycles[i]);
      $display("way [%0d] csb lcycles as zero (values can update): %0d", i, csb_zero_cycles[i]);
    end
    $display("dm_cnt: %0d", dut.mutative_cache0.dm_cnt);
    $display("two_way_cnt: %0d", dut.mutative_cache0.two_way_cnt);
    $display("four_way_cnt: %0d", dut.mutative_cache0.four_way_cnt);
    $display("eight_way_cnt: %0d", dut.mutative_cache0.eight_way_cnt);
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

  if(dut.mutative_cache0.fsm.curr_state == CHECK && dut.mutative_cache0.fsm.cache_hit) begin
    hit_counter++;
  end else if(dut.mutative_cache0.fsm.curr_state == CHECK && !dut.mutative_cache0.fsm.cache_hit) begin
    hit_counter--;
  end

  if(dut.mutative_cache0.fsm.curr_state == IDLE && !dut.mutative_cache0.fsm.flush_stall && dut.mutative_cache0.fsm.cache_request) begin
    request_counter++;
  end
end

  generate
    for (genvar i=0; i<8; ++i) begin
      always @(posedge clk) begin
        if($fell(dut.mutative_cache0.arrays[i].data_array.csb0))
          csb_level_changes_cycles[i] <= csb_level_changes_cycles[i] +1;

        if(!(dut.mutative_cache0.arrays[i].data_array.csb0))
          csb_zero_cycles[i] <= csb_zero_cycles[i] +1;
      end
    end
  endgenerate


endmodule : top_tb