module divider
import rv32imc_types::*;
# (
  parameter NUM_CYCLES = 8
) (
  input logic clk, rst,

  input  logic [31:0] a, 
  input  logic [31:0] b,
  input  logic        start,
  input  logic [2:0]  div_op,
  output logic [31:0] div_fout,
  output logic        div_stall,
  output logic        divide_by_0
);

/* Synopsys Configuration Parameters */
localparam BIT_WIDTH    = 32;
localparam UNSIGNED_DIV = 0;
localparam SIGNED_DIV   = 1;
localparam SYNCH_RST    = 1;

/* Divider Signals */
logic [31:0] udiv_quo, sdiv_quo;
logic [31:0] udiv_rem, sdiv_rem;
logic udiv_exception, sdiv_exception;     // Not Supported
logic div_valid, udiv_valid, sdiv_valid;

/* Divider Execution Logic (Needed Because Non-Pipelined) */
logic div_busy;
always_ff @(posedge clk, posedge rst) begin
  /* Reset when the divider operation completes */
  if (rst) begin
    div_busy <= 1'b0;
  end 
  else if (div_valid) begin
    div_busy <= 1'b0;
  end
  /* Stall until the divider operation completes */
  else if (start) begin
    div_busy <= 1'b1;
  end
end

/* Request & Reply interface assignments */
assign div_valid = (udiv_valid | sdiv_valid) & div_busy;
assign div_stall = (start || div_busy) & ~div_valid;

DW_div_seq #(
  .a_width(BIT_WIDTH),
  .b_width(BIT_WIDTH),
  .tc_mode(UNSIGNED_DIV),
  .num_cyc(NUM_CYCLES),
  .rst_mode(SYNCH_RST)
) udivider0 (
  .clk(clk),
  .rst_n(~rst),
  .hold(~div_busy),
  .start(start),
  .a(a),
  .b(b),
  .complete(udiv_valid),
  .divide_by_0(udiv_exception),
  .quotient(udiv_quo),
  .remainder(udiv_rem)
);

DW_div_seq #(
  .a_width(BIT_WIDTH),
  .b_width(BIT_WIDTH),
  .tc_mode(SIGNED_DIV),
  .num_cyc(NUM_CYCLES),
  .rst_mode(SYNCH_RST)
) sdivider0 (
  .clk(clk),
  .rst_n(~rst),
  .hold(~div_busy),
  .start(start),
  .a(a),
  .b(b),
  .complete(sdiv_valid),
  .divide_by_0(sdiv_exception),
  .quotient(sdiv_quo),
  .remainder(sdiv_rem)
);

/* Exception Logic */
assign divide_by_0 = udiv_exception | sdiv_exception;

/* Result Calculations */
always_comb begin
  unique case (div_op)
    {1'b0, ss_div}: div_fout = sdiv_quo;
    {1'b0, uu_div}: div_fout = udiv_quo;
    {1'b0, ss_rem}: div_fout = sdiv_rem;
    {1'b0, uu_rem}: div_fout = udiv_rem;
    default:        div_fout = 'x;
  endcase
end

endmodule : divider
