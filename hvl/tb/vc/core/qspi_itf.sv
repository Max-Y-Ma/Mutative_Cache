interface qspi_itf();

wire  [3:0] IO;

logic       CLK;
logic       CSn;


modport dut (
  inout IO,
  
  output CLK,
  output CSn
);

modport peripheral (
  inout  IO,
  
  input  CLK,
  input  CSn
);

modport mon (
  input  IO,

  input  CLK,
  input  CSn
);

endinterface
