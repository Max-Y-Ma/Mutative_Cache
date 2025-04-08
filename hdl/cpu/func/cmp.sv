module cmp
import rv32imc_types::*;
(
  input  logic [31:0] a, 
  input  logic [31:0] b,
  input  logic [2:0]  cmp_op,
  output logic        br_en
);

logic signed   [31:0] as;
logic signed   [31:0] bs;
logic unsigned [31:0] au;
logic unsigned [31:0] bu;

assign as = signed'(a);
assign bs = signed'(b);
assign au = unsigned'(a);
assign bu = unsigned'(b);

// Comparator Operations
always_comb begin
  unique case (cmp_op)
    beq:  br_en = (au == bu);
    bne:  br_en = (au != bu);
    blt:  br_en = (as < bs);
    bge:  br_en = (as >= bs);
    bltu: br_en = (au < bu);
    bgeu: br_en = (au >= bu);
    default: br_en = 1'bx;
  endcase
end

endmodule : cmp
