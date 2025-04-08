// Decodes RISC-V compressed instructions into their RV32 equivalent.
module compressed_decoder 
import rv32imc_types::*;
(
  input  logic [31:0] i_instr,
  output logic [31:0] o_instr,
  output logic        o_compressed,
  output logic        o_illegal
);

  // Compressed instruction have least significant two bits as b00, b01, or b10
  assign o_compressed = (i_instr[1:0] != 2'b11);

  // Compressed instruction format fields
  logic [1:0] opcode;
  logic [2:0] funct3;
  assign opcode = i_instr[1:0];
  assign funct3 = i_instr[15:13];

  // Decode a given compressed instruction into regular instruction format
  always_comb begin
    // By default, forward incoming instruction, mark it as legal.
    o_instr   = i_instr;
    o_illegal = 1'b0;

    unique case (opcode)
      c0: begin
        unique case (funct3)
          c_addi4spn: begin
            // c.addi4spn -> addi rd', x2, imm
            o_instr = {
              2'b0, i_instr[10:7], i_instr[12:11], i_instr[5], i_instr[6], 
              2'b00, 5'b00010, 3'b000, 2'b01, i_instr[4:2], op_imm
            };

            if (i_instr[12:5] == 8'b0) begin
              o_illegal = 1'b1;
            end
          end
          c_lw: begin
            // c.lw -> lw rd', imm(rs1')
            o_instr = {
              5'b0, i_instr[5], i_instr[12:10], i_instr[6], 2'b00, 2'b01, 
              i_instr[9:7], 3'b010, 2'b01, i_instr[4:2], op_load
            };
          end
          c_sw: begin
            // c.sw -> sw rs2', imm(rs1')
            o_instr = {
              5'b0, i_instr[5], i_instr[12], 2'b01, i_instr[4:2], 2'b01, 
              i_instr[9:7], 3'b010, i_instr[11:10], i_instr[6], 2'b00, op_store
            };
          end
          default: begin
            o_illegal = 1'b1;
          end
        endcase
      end
      c1: begin
        unique case (funct3)
          c_addi: begin
            // c.addi -> addi rd, rd, nzimm
            // c.nop
            o_instr = {
              {6{i_instr[12]}}, i_instr[12], i_instr[6:2], i_instr[11:7], 
              3'b000, i_instr[11:7], op_imm
            };
          end
          c_jal, c_j: begin
            // c.jal -> jal x1, imm
            // c.j   -> jal x0, imm
            o_instr = {
              i_instr[12], i_instr[8], i_instr[10:9], i_instr[6], i_instr[7], 
              i_instr[2], i_instr[11], i_instr[5:3], {9{i_instr[12]}}, 
              4'b0000, ~i_instr[15], op_jal
            };
          end
          c_li: begin
            // c.li -> addi rd, x0, nzimm
            o_instr = {
              {6{i_instr[12]}}, i_instr[12], i_instr[6:2], 5'b00000,
              3'b000, i_instr[11:7], op_imm
            };
          end
          c_lui: begin
            // c.lui -> lui rd, imm
            o_instr = {
              {15{i_instr[12]}}, i_instr[6:2], i_instr[11:7], op_lui
            };

            if (i_instr[11:7] == 5'b00010) begin
              // c.addi16sp -> addi x2, x2, nzimm
              o_instr = {
                {3{i_instr[12]}}, i_instr[4:3], i_instr[5], i_instr[2],
                i_instr[6], 4'b0000, 5'b00010, 3'b000, 5'b00010, op_imm
              };
            end

            if ({i_instr[12], i_instr[6:2]} == 6'b000000) begin
              o_illegal = 1'b1;
            end
          end
          c_logic: begin
            unique case (i_instr[11:10])
              c_srli, c_srai: begin
                // c.srli -> srli rd, rd, shamt
                // c.srai -> srai rd, rd, shamt
                o_instr = {
                  1'b0, i_instr[10], 5'b00000, i_instr[6:2], 2'b01, 
                  i_instr[9:7], 3'b101, 2'b01, i_instr[9:7], op_imm
                };

                if (i_instr[12] == 1'b1) begin
                  o_illegal = 1'b1;
                end
              end
              c_andi: begin
                // c.andi -> andi rd, rd, imm
                o_instr = {
                  {6{i_instr[12]}}, i_instr[12], i_instr[6:2], 2'b01, 
                  i_instr[9:7], 3'b111, 2'b01, i_instr[9:7], op_imm
                };
              end
              c_sxoa: begin
                unique case ({i_instr[12], i_instr[6:5]})
                  c_sub: begin
                    // c.sub -> sub rd', rd', rs2'
                    o_instr = {
                      2'b01, 5'b00000, 2'b01, i_instr[4:2], 2'b01, i_instr[9:7],
                      3'b000, 2'b01, i_instr[9:7], op_reg
                    };
                  end
                  c_xor: begin
                    // c.xor -> xor rd', rd', rs2'
                    o_instr = {
                      7'b0000000, 2'b01, i_instr[4:2], 2'b01, i_instr[9:7], 
                      3'b100, 2'b01, i_instr[9:7], op_reg
                    };
                  end
                  c_or: begin
                    // c.or  -> or  rd', rd', rs2'
                    o_instr = {
                      7'b0000000, 2'b01, i_instr[4:2], 2'b01, i_instr[9:7], 
                      3'b110, 2'b01, i_instr[9:7], op_reg
                    };
                  end
                  c_and: begin
                    // c.and -> and rd', rd', rs2'
                    o_instr = {
                      7'b0000000, 2'b01, i_instr[4:2], 2'b01, i_instr[9:7], 
                      3'b111, 2'b01, i_instr[9:7], op_reg
                    };
                  end
                  default: begin
                    o_illegal = 1'b1;
                  end
                endcase
              end
              default: begin
                o_illegal = 1'b1;
              end
            endcase
          end
          c_beqz, c_bnez: begin
            // c.beqz -> beq rs1', x0, imm
            // c.bnez -> bne rs1', x0, imm
            o_instr = {
              {4{i_instr[12]}}, i_instr[6:5], i_instr[2], 5'b00000, 2'b01, 
              i_instr[9:7], 2'b00, i_instr[13], i_instr[11:10], i_instr[4:3],
              i_instr[12], op_br
            };
          end
          default: begin
            o_illegal = 1'b1;
          end
        endcase
      end
      c2: begin
        unique case (funct3)
          c_slli: begin
            // c.slli -> slli rd, rd, shamt
            o_instr = {
              7'b0000000, i_instr[6:2], i_instr[11:7], 3'b001, i_instr[11:7], 
              op_imm
            };

            if (i_instr[12] == 1'b1) begin
              o_illegal = 1'b1; // reserved for custom extensions
            end
          end
          c_lwsp: begin
            // c.lwsp -> lw rd, imm(x2)
            o_instr = {
              4'b0000, i_instr[3:2], i_instr[12], i_instr[6:4], 2'b00, 
              5'b00010, 3'b010, i_instr[11:7], op_load
            };

            if (i_instr[11:7] == 5'b0) begin
              o_illegal = 1'b1;
            end
          end
         c_other: begin
            if (i_instr[12] == 1'b0) begin
              if (i_instr[6:2] != 5'b0) begin
                // c.mv -> add rd/rs1, x0, rs2
                o_instr = {
                  7'b0000000, i_instr[6:2], 5'b00000, 3'b000, i_instr[11:7], 
                  op_reg
                };
              end else begin
                // c.jr -> jalr x0, rd/rs1, 0
                o_instr = {
                  12'b000000000000, i_instr[11:7], 3'b000, 5'b00000, op_jalr
                };

                if (i_instr[11:7] == 5'b0) begin
                  o_illegal = 1'b1;
                end
              end
            end else begin
              if (i_instr[6:2] != 5'b0) begin
                // c.add -> add rd, rd, rs2
                o_instr = {
                  7'b0000000, i_instr[6:2], i_instr[11:7], 3'b000, 
                  i_instr[11:7], op_reg
                };
              end else begin
                // c.jalr -> jalr x1, rs1, 0
                o_instr = {
                  12'b000000000000, i_instr[11:7], 3'b000, 5'b00001, op_jalr
                };
              end
            end
          end
          c_swsp: begin
            // c.swsp -> sw rs2, imm(x2)
            o_instr = {
              4'b0000, i_instr[8:7], i_instr[12], i_instr[6:2], 5'b00010, 
              3'b010, i_instr[11:9], 2'b00, op_store
            };
          end
          default: begin
            o_illegal = 1'b1;
          end
        endcase
      end
      // Incoming instruction is not compressed.
      c3:;
      default: begin
        o_illegal = 1'b1;
      end
    endcase
  end

endmodule : compressed_decoder
