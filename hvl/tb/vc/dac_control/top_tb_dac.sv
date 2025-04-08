module top_tb_dac;

timeunit      1ps;
timeprecision 1ps;

localparam NUM_TESTS = 100;

bit clk;
bit rst;
logic [7:0] binary_in;
logic       thermometer_out   [255:1];
logic       thermometer_out_b [255:1];

int clock_half_period_ps = 5;
int counter;

initial begin
  clk = 1'b0;
  forever begin
    #(clock_half_period_ps) clk = ~clk;
  end
end

initial begin
  $fsdbDumpfile("dump.fsdb");
  $fsdbDumpvars(0, "+all");
  rst = 1'b0;
  repeat (3) @(posedge clk);
  rst = 1'b1;
end

initial begin
  repeat(3) @(posedge clk);
  for (int binary = 0; binary < 256; binary++) begin
    binary_in <= binary;
    @(posedge clk);
    #1;
    // Check output is correct
    for (int i = 1; i < 256; i++) begin
      if ($isunknown(thermometer_out[i]) || $isunknown(thermometer_out_b[i])) begin
        $fatal("Unknown Value");
      end
      if (i > binary_in) begin
        if (thermometer_out[i] != 1'b0) begin
          $fatal("Incorrect Thermometer Zero Value");
        end
        if (thermometer_out_b[i] != 1'b1) begin
          $fatal("Incorrect Thermometer_b One Value");
        end
      end
      else begin
        if (thermometer_out[i] != 1'b1) begin
          $fatal("Incorrect Thermometer One Value");
        end
        if (thermometer_out_b[i] != 1'b0) begin
          $fatal("Incorrect Thermometer_b Zero Value");
        end
      end
    end
  end
  $display("All Tests Passed! Yay");
  $finish();
end

dac_control control0 (
  .clk(clk),
  .rst(rst),
  .binary(binary_in),
  .current_enable(thermometer_out),
  .current_enable_b(thermometer_out_b)
);

endmodule : top_tb_dac
