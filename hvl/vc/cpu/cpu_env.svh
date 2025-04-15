// Environment Class for RISCV Pipeline CPU
class cpu_coverage extends uvm_subscriber #(cpu_rand_instr);
  `uvm_component_utils(cpu_coverage)

  // Analysis Port
  uvm_analysis_port #(cpu_rand_instr) aport;

  // Covergroup
  covergroup instr_cg with function sample(instr_t instr);
    // Easy covergroup to see that we're at least exercising
    // every opcode. Since opcode is an enum, this makes bins
    // for all its members.
    all_opcodes : coverpoint instr.i_type.opcode;

    // Some simple coverpoints on various instruction fields.
    // Recognize that these coverpoints are inherently less useful
    // because they really make sense in the context of the opcode itself.
    all_funct7 : coverpoint funct7_t'(instr.r_type.funct7);

    // Check that funct3 takes on all possible values.
    all_funct3 : coverpoint instr.i_type.funct3;

    // Check that the rs1 and rs2 fields across instructions take on
    // all possible values (each register is touched).
    all_regs_rs1 : coverpoint instr.r_type.rs1;
    all_regs_rs2 : coverpoint instr.r_type.rs2;
    all_regs_rd  : coverpoint instr.r_type.rd;

    // Now, cross coverage takes in the opcode context to correctly
    // figure out the /real/ coverage.
    funct3_cross : cross instr.i_type.opcode, instr.i_type.funct3 {
      // We want to ignore the cases where funct3 isn't relevant.
      // For example, for JAL, funct3 doesn't exist. Put it in an ignore_bins.
      ignore_bins JAL_FUNCT3 = funct3_cross with (instr.i_type.opcode == op_jal);
      ignore_bins LUI_FUNCT3 = funct3_cross with (instr.i_type.opcode == op_lui);
      ignore_bins AUIPC_FUNCT3 = funct3_cross with (instr.i_type.opcode == op_auipc);

      // Branch instructions use funct3, but only 6 of the 8 possible values
      // are valid. Ignore the other two -- don't include them in the coverage
      // report. In fact, if they're generated, that's an illegal instruction.
      illegal_bins BR_FUNCT3 = funct3_cross with
      (instr.i_type.opcode == op_br
      && !(instr.i_type.funct3 inside {beq, bne, blt, bge, bltu, bgeu}));

      // Ignore all other combinations of JALR instructions
      illegal_bins JALR_FUNCT3 = funct3_cross with 
      (instr.i_type.opcode == op_jalr && instr.i_type.funct3 != 3'b000);

      // Ignore all other combinations of LOAD instructions
      illegal_bins LOAD_FUNCT3 = funct3_cross with 
      (instr.i_type.opcode == op_load && !(instr.i_type.funct3 inside {lb, lh, lw, lbu, lhu}));

      // Ignore all other combinations of STORE instructions
      illegal_bins STORE_FUNCT3 = funct3_cross with 
      (instr.i_type.opcode == op_store && !(instr.i_type.funct3 inside {sb, sh, sw}));
    }

    // Coverpoint to make separate bins for funct7.
    coverpoint instr.r_type.funct7 {
      bins range[] = {[0:$]};
      ignore_bins not_in_spec = {[1:31], [33:127]};
    }

    // Cross coverage for funct7.
    funct7_cross : cross instr.r_type.opcode, instr.r_type.funct3, instr.r_type.funct7 {
      // No opcodes except op_reg and op_imm use funct7, so ignore the rest.
      ignore_bins OTHER_INSTS = funct7_cross with
      (!(instr.r_type.opcode inside {op_reg, op_imm}));

      // Ignore op_imm other than SLLI, SRLI, and SRAI
      ignore_bins OP_IMM_FUNCT7 = funct7_cross with
      (instr.r_type.opcode == op_imm && !(instr.r_type.funct3 inside {slli, sri}));

      // Ignore SLLI with variant funct7
      ignore_bins OP_SLLI_FUNCT7 = funct7_cross with
      (instr.r_type.opcode == op_imm && instr.r_type.funct3 == slli && instr.r_type.funct7 == variant);

      // Ignore op_reg with funct7 other than ADD and SR with variant funct7
      ignore_bins OP_REG_FUNCT7 = funct7_cross with
      (instr.r_type.opcode == op_reg && !(instr.r_type.funct3 inside {addr, srr}) 
      && (instr.r_type.funct7 == variant));
    }
  endgroup : instr_cg

  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
    instr_cg = new();
  endfunction : new

  // Create Port
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Create Analysis Port
    aport = new("aport", this);
  endfunction : build_phase

  // Sample Data
  function void write(cpu_rand_instr t);
    // Sample Data
    instr_cg.sample(t.instr.instr);
  endfunction : write

endclass : cpu_coverage

class cpu_env extends uvm_env;
  `uvm_component_utils(cpu_env)

  // Agent, Coverage
  cpu_agent agent;
  cpu_coverage coverage;

  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Factory Build
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = cpu_agent::type_id::create("agent", this);
    coverage = cpu_coverage::type_id::create("coverage", this);
  endfunction : build_phase

  // Connect Analysis Port
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect Coverage Analysis Ports
    agent.aport.connect(coverage.analysis_export);
  endfunction : connect_phase

endclass : cpu_env