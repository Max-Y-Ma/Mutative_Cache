interface qspi_itf;

wire  [3:0] io;
logic       clk;
logic       csn;


modport dut (
  inout io,
  
  output clk,
  output csn
);

modport peripheral (
  inout  io,
  
  input  clk,
  input  csn
);

modport mon (
  input  io,

  input  clk,
  input  csn
);

endinterface
