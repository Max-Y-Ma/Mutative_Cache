module multiplier
import rv32imc_types::*;
# (
  parameter DEPTH = 2
) (
  input logic clk, rst,

  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic        start,
  input  logic [2:0]  mul_op,
  input  logic [2:0]  mul_funct3,
  output logic [31:0] mul_fout,
  output logic        mul_stall
);

/* Stall Signal */
logic mul_busy;
logic done [DEPTH+1:0];
always_ff @ (posedge clk) begin
  /* Reset when the multiplier operation completes */
  if (rst || done[DEPTH+1]) begin
    mul_busy <= '0;
  end
  /* Stall until the multiplication operation completes */
  else if (start) begin
    mul_busy <= '1;
  end
end

assign mul_stall = (start || mul_busy) & ~done[DEPTH+1];
assign done[0]   = start & ~mul_busy;

/* Pipeline Signals */
logic [63:0] mul_result [DEPTH+1:0];
always_ff @ (posedge clk) begin
  for (integer i = 0; i < DEPTH+1; i++) begin
    if (rst) begin
      mul_result[i+1] <= '0;
      done[i+1] <= '0;
    end
    else begin
      mul_result[i+1] <= mul_result[i];
      done[i+1] <= done[i];
    end
  end
end

multiplier_combinational multiplier_combinational0 (
  .a(a),
  .b(b),
  .mul_type(mul_op[1:0]),
  .p(mul_result[0])
);

/* Output Logic */
logic [63:0] mul_p;
assign mul_p = mul_result[DEPTH+1];

always_comb begin
  unique case (mul_funct3)
    mulr    : mul_fout = mul_p[31:0];
    mulhr   : mul_fout = mul_p[63:32];
    mulhsur : mul_fout = mul_p[63:32];
    mulhur  : mul_fout = mul_p[63:32];
    default        : mul_fout = 'x;
  endcase
end

endmodule : multiplier
