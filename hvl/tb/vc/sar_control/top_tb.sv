module top_tb;

timeunit 1ps;
timeprecision 1ps;

parameter WIDTH = 3;

int clock_half_period_ps = 1000;

bit clk;
always #(clock_half_period_ps) clk = ~clk;

bit rst;

logic adc_en;
logic comp_result;

logic s_in;
logic s_c;
logic [2:0][WIDTH-1:0] dac_switches;
logic [2:0] dummy_switch;

logic eoc_n;
logic load_reg;
logic [WIDTH-1:0] reg_wdata;

// DUT Instantiation
sar_control #(.WIDTH(WIDTH)) dut (
  .clk(clk),
  .rst_n(~rst),
  .adc_en(adc_en),
  .comp_result(comp_result),

  .s_in(s_in),
  .s_c(s_c),
  .dac_switches(dac_switches),
  .dummy_switch(dummy_switch),
  .eoc_n(eoc_n),
  .load_reg(load_reg),
  .reg_wdata(reg_wdata)
);

always_ff @ (posedge clk) begin
  comp_result <= $urandom_range(0,1);
  //comp_result <= 1'b0;
end

initial begin
  $fsdbDumpfile("dump.fsdb");
  $fsdbDumpvars(0, "+all");
  rst = 1'b1;
  adc_en = 1'b0;
  repeat (2) @(posedge clk);
  rst <= 1'b0;
  @(posedge clk);
  adc_en <= 1'b1;

  repeat (100) @(posedge clk);
  $finish;
end

endmodule : top_tb
