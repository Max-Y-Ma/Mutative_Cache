// Random Valid RISC-V instructions for RISV Pipeline CPU
class randInstr;
  // Number of instruction types
  localparam NUM_TYPES = 9;

  // Randomization Variables
  rand instr_t instr;
  rand bit [NUM_TYPES-1:0] instr_type;

  // Make sure we have an even distribution of instruction types.
  constraint solve_order_c { solve instr_type before instr; }

  // Make sure to solve funct3 before funct7
  rand bit [2:0] funct3;
  rand bit [6:0] funct7;
  constraint solve_order_funct3_c { 
    // Solve order constraint
    funct3 == instr.r_type.funct3;
    funct7 == instr.r_type.funct7;
    solve funct3 before funct7; 
  }

  // Pick one of the instruction types.
  constraint instr_type_c {
    $countones(instr_type) == 1; // Ensures one-hot.
  }

  // Constraints for actually generating instructions, given the type.
  constraint instr_c {
    // Reg-imm instructions
    instr_type[0] -> {
      instr.i_type.opcode == op_imm;

      // Implies syntax: if funct3 is sr, then funct7 must be
      // one of two possibilities.
      instr.r_type.funct3 == sri -> {
        instr.r_type.funct7 inside {base, variant};
      }

      // This if syntax is equivalent to the implies syntax above
      // but also supports an else { ... } clause.
      if (instr.r_type.funct3 == slli) {
        instr.r_type.funct7 == base;
      }
    }

    // Reg-reg instructions
    instr_type[1] -> {
      instr.r_type.opcode == op_reg;

      // Adjust Funct7 for M and I extension variants
      if (instr.r_type.funct3 inside {addr, srr} ) {
        instr.r_type.funct7 inside {base, variant, mult_variant};
      } else if (instr.r_type.funct3 inside {sllr, sltr, sltru, xorr, orr, andr}) {
        instr.r_type.funct7 inside {base, mult_variant};
      } else {
        instr.r_type.funct7 == base;
      }
    }

    // Store instructions -- these are easy to constrain!
    instr_type[2] -> {
      instr.s_type.opcode == op_store;
      instr.s_type.funct3 inside {sw, sb, sh};

      // Constraint rs1 equal to x0
      instr.s_type.rs1 == '0;

      // Constraint immediate to 2-byte or 4-byte alignment
      (instr.s_type.funct3 == sw) -> {
        instr.s_type.imm_s_bot[1:0] == 2'b00;
      }

      (instr.s_type.funct3 == sh) -> {
        instr.s_type.imm_s_bot[1:0] inside {2'b00, 2'b10};
      }
    }

    // Load instructions
    instr_type[3] -> {
      instr.i_type.opcode == op_load;
      instr.i_type.funct3 inside {lb, lh, lw, lbu, lhu};

      // Constraint rs1 equal to x0
      instr.i_type.rs1 == '0;

      // Constraint immediate to 2-byte or 4-byte alignment
      (instr.i_type.funct3 == lw) -> {
        instr.i_type.i_imm[1:0] == 2'b00;
      }

      (instr.i_type.funct3 == lh || instr.i_type.funct3 == lhu) -> {
        instr.i_type.i_imm[1:0] inside {2'b00, 2'b10};
      }
    }

    // Branch instructions
    instr_type[4] -> {
      instr.b_type.opcode == op_br;
      instr.b_type.funct3 inside {beq, bne, blt, bge, bltu, bgeu};
      instr.b_type.imm_b_bot != '0;
      instr.b_type.imm_b_bot[1:0] == 2'b00;
    }

    // LUI instruction
    instr_type[5] -> {
      instr.j_type.opcode == op_lui;
      instr.j_type.imm != '0;
      instr.j_type.imm[21] == 1'b0;
    }

    // AUIPC instruction
    instr_type[6] -> {
      instr.j_type.opcode == op_auipc;
    }

    // JAL instruction
    instr_type[7] -> {
      instr.j_type.opcode == op_jal;
    }

    // JALR instruction
    instr_type[8] -> {
      instr.i_type.opcode == op_jalr;
      instr.i_type.funct3 == 3'b000;
      instr.i_type.i_imm[1:0] == 2'b00;
      instr.i_type.i_imm != '0;
    }
  }

endclass : randInstr

class cpu_rand_instr extends uvm_sequence_item;
  `uvm_object_utils(cpu_rand_instr)

  randInstr instr;

  // Constructor
  function new(string name = "");
      super.new(name);
      instr = new();
  endfunction : new

  // Sequence Functions
  virtual function void do_copy(uvm_object rhs);
      // Copy argument data to current object
      cpu_rand_instr RHS;
      if (!$cast(RHS, rhs)) begin
          uvm_report_error("do_copy:", "Cast Failed");
          return;
      end
      super.do_copy(rhs);
      instr = RHS.instr;
  endfunction : do_copy

  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
      // Compare argument data with current object
      cpu_rand_instr RHS;
      if (!$cast(RHS, rhs)) begin
          uvm_report_error("do_compare:", "Cast Failed");
          return 0;
      end
      return (super.do_compare(rhs, comparer) && (instr == RHS.instr));
  endfunction : do_compare

  virtual function string convert2string();
      // Stringify current object
      string s;
      s = super.convert2string();
      s = {s, $sformatf("instr = %p", instr)};
      return s;
  endfunction : convert2string

endclass : cpu_rand_instr
