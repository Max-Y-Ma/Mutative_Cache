import "DPI-C" function string getenv(input string env_name);

module top_tb;

timeunit 1ps;
timeprecision 1ps;

// Clock Generation
// int clock_half_period_ps = getenv("ECE411_CLOCK_PERIOD_PS").atoi() / 2;
int clock_half_period_ps = 6_250 / 2; // Run sim at 160 MHz, near flash max freq

bit clk;
always #(clock_half_period_ps) clk = ~clk;

bit rst;

// QSPI Flash Interface
qspi_itf flash_itf();

// Monitor Interface
mon_itf mon_itf(.*);    
monitor monitor(.itf(mon_itf));

W25Q128JVxIQ flash(
  .CSn(flash_itf.CSn),
  .CLK(flash_itf.CLK),
  .DIO(flash_itf.IO[0]),
  .DO(flash_itf.IO[1]),
  .WPn(flash_itf.IO[2]),
  .HOLDn(flash_itf.IO[3])
);

// DUT Instantiation
core dut(
  .clk_i(clk),
  .rst_i(rst),
  .qspi_io_io(flash_itf.IO),
  .qspi_ck_o(flash_itf.CLK),
  .qspi_cs_o(flash_itf.CSn)
);

// Monitor Interface DUT Wiring
`include "../../chip/tb/vc/core/rvfi_reference.svh"

// Waveform Dumpfiles and Reset
initial begin
  $fsdbDumpfile("dump.fsdb");
  // $fsdbDumpvars(0, "+all");
  $fsdbDumpvars(0, top_tb.flash_itf);
  $fsdbDumpvars(0, top_tb.mon_itf);
  $fsdbDumpvars(0, top_tb.monitor);
  $fsdbDumpvars(0, top_tb.dut);

  $dumpfile("dump.vcd");
  $dumpvars();
  
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
  timeout_cycles <= timeout_cycles - 1;
end

endmodule : top_tb
