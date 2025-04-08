module top_tb;

timeunit 1ps;
timeprecision 1ps;

parameter WIDTH = 3;

int clock_half_period_ps = 1000;

bit CLK;
always #(clock_half_period_ps) CLK = ~CLK;

bit RST;

logic FIRM_EN;
logic ADC_EN;
logic CALIB_EN;
logic COMP_RESULT; 
 
logic S_C;

logic EOC_N;

logic [1:0] DAC_SWITCHES_TOP_0;
logic [1:0] DAC_SWITCHES_BOT_0;
logic [1:0] DAC_SWITCHES_TOP_1;
logic [1:0] DAC_SWITCHES_BOT_1;
logic [1:0] DAC_SWITCHES_TOP_2;
logic [1:0] DAC_SWITCHES_BOT_2;
logic [1:0] DAC_SWITCHES_TOP_3;
logic [1:0] DAC_SWITCHES_BOT_3;
logic [1:0] DAC_SWITCHES_TOP_4;
logic [1:0] DAC_SWITCHES_BOT_4;
logic [1:0] DAC_SWITCHES_TOP_5;
logic [1:0] DAC_SWITCHES_BOT_5;
logic [1:0] DAC_SWITCHES_TOP_6;
logic [1:0] DAC_SWITCHES_BOT_6;
logic [1:0] DAC_SWITCHES_TOP_7;
logic [1:0] DAC_SWITCHES_BOT_7;
logic [1:0] DUMMY_SWITCH_TOP;
logic [1:0] DUMMY_SWITCH_BOT;

// DUT Instantiation
adc_cap_dac_8_bit_diff_digital_top dut0 (
  .CLK(CLK),
  .RST(RST),
  .FIRM_EN(FIRM_EN),
  .ADC_EN(ADC_EN),
  .CALIB_EN(CALIB_EN),

  .COMP_RESULT(COMP_RESULT),
  .S_C(S_C),
  .DAC_SWITCHES_TOP_0(DAC_SWITCHES_TOP_0),
  .DAC_SWITCHES_BOT_0(DAC_SWITCHES_BOT_0),
  .DAC_SWITCHES_TOP_1(DAC_SWITCHES_TOP_1),
  .DAC_SWITCHES_BOT_1(DAC_SWITCHES_BOT_1),
  .DAC_SWITCHES_TOP_2(DAC_SWITCHES_TOP_2),
  .DAC_SWITCHES_BOT_2(DAC_SWITCHES_BOT_2),
  .DAC_SWITCHES_TOP_3(DAC_SWITCHES_TOP_3),
  .DAC_SWITCHES_BOT_3(DAC_SWITCHES_BOT_3),
  .DAC_SWITCHES_TOP_4(DAC_SWITCHES_TOP_4),
  .DAC_SWITCHES_BOT_4(DAC_SWITCHES_BOT_4),
  .DAC_SWITCHES_TOP_5(DAC_SWITCHES_TOP_5),
  .DAC_SWITCHES_BOT_5(DAC_SWITCHES_BOT_5),
  .DAC_SWITCHES_TOP_6(DAC_SWITCHES_TOP_6),
  .DAC_SWITCHES_BOT_6(DAC_SWITCHES_BOT_6),
  .DAC_SWITCHES_TOP_7(DAC_SWITCHES_TOP_7),
  .DAC_SWITCHES_BOT_7(DAC_SWITCHES_BOT_7),
  .DUMMY_SWITCH_TOP(DUMMY_SWITCH_TOP),
  .DUMMY_SWITCH_BOT(DUMMY_SWITCH_BOT)
);

always_ff @ (posedge CLK) begin
  COMP_RESULT <= ~$urandom_range(0,1);
  //comp_result <= 1'b0;
end

initial begin
  $fsdbDumpfile("dump.fsdb");
  $fsdbDumpvars(0, "+all");
  RST = 1'b1;
  ADC_EN = 1'b0;
  CALIB_EN = 1'b0;
  FIRM_EN = 1'b1;
  repeat (2) @(posedge CLK);
  RST <= 1'b0;
  @(posedge CLK);
  CALIB_EN <= 1'b1;
  ADC_EN <= 1'b1;
  @(posedge CLK);
  CALIB_EN <= 1'b0;

  repeat (30) @(posedge CLK);
  CALIB_EN <= 1'b1;
  repeat (30) @(posedge CLK);
  CALIB_EN <= 1'b0;
  repeat (30) @(posedge CLK);
  CALIB_EN <= 1'b1;
  repeat (30) @(posedge CLK);
  CALIB_EN <= 1'b0;
  FIRM_EN <= 1'b0;

  repeat (100) @(posedge CLK);
  RST <= 1'b1;
  repeat (5) @(posedge CLK);
  RST <= 1'b0;

  repeat (1000) @(posedge CLK);
  $finish;
end

endmodule : top_tb
