module top_tb;

timeunit 1ps;
timeprecision 1ps;

// include uart tasks 
`include "uart_tasks.v" 

// Clock Generation
int clock_half_period_ps = 8_000 / 2; // Run sim at 125MHz

bit clk;
always #(clock_half_period_ps) clk = ~clk;

bit rst;

// UART Signals
logic tx, rx;

// Memory map signals
logic [31:0] mem_addr;
logic [3:0]  mem_rmask;
logic [3:0]  mem_wmask;
logic [31:0] mem_rdata;
logic [31:0] mem_wdata;
logic        mem_resp;

assign rx = serial_out;
always @ (posedge clk) serial_in = tx;

// Instantiate DUT
uart_peripheral dut (
  .clk(clk),
  .rst(rst),

  .rx(rx),
  .tx(tx),

  /* Connection to memory map */
  .mem_addr(mem_addr),
  .mem_rmask(mem_rmask),
  .mem_wmask(mem_wmask),
  .mem_rdata(mem_rdata),
  .mem_wdata(mem_wdata),
  .mem_resp(mem_resp)
);

// Waveform Dumpfiles and Reset
initial begin
  $fsdbDumpfile("dump.fsdb");
  $fsdbDumpvars(0, "+all");
   
  rst = 1'b1;
  repeat (2) @(posedge clk);
  rst <= 1'b0;
end

initial begin
  mem_addr  = 'x;
  mem_rmask = '0;
  mem_wmask = '0;
  mem_wdata = 'x;

  send_serial(8'h55, `BAUD_115200, `PARITY_EVEN, `PARITY_OFF, `NSTOPS_1, `NBITS_8, 0);

  @(posedge clk);
  mem_addr  = '0;
  mem_rmask = '1;
  mem_wmask = '0;
  mem_wdata = 'x;

  @(posedge clk);
  mem_rmask = '0;

  @(posedge mem_resp);

  $display("Written val %x", mem_rdata);

  @(posedge clk);
  mem_rmask = '1;
  @(posedge clk);
  mem_rmask = '1;

  @(posedge mem_resp);

  $display("Written val %x", mem_rdata);

  repeat(5) @(posedge clk);

  $finish;
end

endmodule : top_tb
