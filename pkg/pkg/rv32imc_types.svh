package rv32imc_types;

/******************************************************************************\
  Instruction format typedefs
\******************************************************************************/
typedef enum bit [6:0] {
  op_lui   = 7'b0110111, // U load upper immediate 
  op_auipc = 7'b0010111, // U add upper immediate PC 
  op_jal   = 7'b1101111, // J jump and link 
  op_jalr  = 7'b1100111, // I jump and link register 
  op_br    = 7'b1100011, // B branch 
  op_load  = 7'b0000011, // I load 
  op_store = 7'b0100011, // S store 
  op_imm   = 7'b0010011, // I arith ops with register/immediate operands 
  op_reg   = 7'b0110011, // R arith ops with register operands 
  op_mret  = 7'b1110011  //
} rv32im_inst_opcode_t;

typedef enum bit [24:0]{
  valid_int_opcode = 25'b0011000000100000000000000
} ret_bits_t;

typedef enum bit [1:0] {
  c0 = 2'b00, // Indicates compressed instruction
  c1 = 2'b01, // Indicates compressed instruction
  c2 = 2'b10, // Indicates compressed instruction
  c3 = 2'b11  // Indicates regular instruction
} rv32c_inst_opcode_t;

typedef enum bit [2:0] {
  c_addi4spn  = 3'b000,
  c_lw        = 3'b010,
  c_sw        = 3'b110
} c0_funct3_t;

typedef enum bit [2:0] {
  c_addi  = 3'b000,
  c_jal   = 3'b001,
  c_li    = 3'b010,
  c_lui   = 3'b011,
  c_logic = 3'b100,
  c_j     = 3'b101,
  c_beqz  = 3'b110,
  c_bnez  = 3'b111
} c1_funct3_t;

typedef enum bit [1:0] {
  c_srli = 2'b00,
  c_srai = 2'b01,
  c_andi = 2'b10,
  c_sxoa = 2'b11
} c1_logic_t;

typedef enum bit [2:0] {
  c_sub = 3'b000,
  c_xor = 3'b001,
  c_or  = 3'b010,
  c_and = 3'b011
} c1_logic_funct3_t;

typedef enum bit [2:0] {
  c_slli  = 3'b000,
  c_lwsp  = 3'b010,
  c_other = 3'b100,
  c_swsp  = 3'b110
} c2_funct3_t;

typedef enum bit [2:0] {
  alu_add = 3'b000, // Check bit 30 for add/sub
  alu_sll = 3'b001,
  alu_sra = 3'b010,
  alu_sub = 3'b011,
  alu_xor = 3'b100,
  alu_srl = 3'b101, // Check bit 30 for logical/arithmetic
  alu_or  = 3'b110,
  alu_and = 3'b111
} rv32_alu_opcode_t;

typedef enum bit [2:0] {
  beq  = 3'b000,
  bne  = 3'b001,
  blt  = 3'b100,
  bge  = 3'b101,
  bltu = 3'b110,
  bgeu = 3'b111
} branch_funct3_t;

typedef enum bit [2:0] {
  lb  = 3'b000,
  lh  = 3'b001,
  lw  = 3'b010,
  lbu = 3'b100,
  lhu = 3'b101
} load_funct3_t;

typedef enum bit [2:0] {
  sb = 3'b000,
  sh = 3'b001,
  sw = 3'b010
} store_funct3_t;

typedef enum bit [2:0] {
  addi  = 3'b000,
  slli  = 3'b001,
  slti  = 3'b010,
  sltiu = 3'b011,
  xori  = 3'b100,
  sri   = 3'b101, // Check bit 30 for logical/arithmetic
  ori   = 3'b110,
  andi  = 3'b111
} arith_imm_funct3_t;

typedef enum bit [2:0] {
  addr   = 3'b000, // Check bit 30 and 25 for add, subtract, or multiply
  sllr   = 3'b001, // Check bit 25 for multiply
  sltr   = 3'b010, // Check bit 25 for multiply
  sltru  = 3'b011, // Check bit 25 for multiply
  xorr   = 3'b100, // Check bit 25 for divide
  srr    = 3'b101, // Check bit 30 for logical/arithmetic or Check bit 25 for divide
  orr    = 3'b110, // Check bit 25 for divide
  andr   = 3'b111  // Check bit 25 for divide
} arith_reg_funct3_t;

typedef enum bit [2:0] {
  mulr    = 3'b000,
  mulhr   = 3'b001,
  mulhsur = 3'b010,
  mulhur  = 3'b011
} arith_mul_funct3_t;

typedef enum bit [1:0] { 
  uu_mul = 2'b00,
  ss_mul = 2'b01,
  su_mul = 2'b10
} mul_type_t;

typedef enum bit [1:0] {
  ss_div = 2'b00,
  uu_div = 2'b01,
  ss_rem = 2'b10,
  uu_rem = 2'b11
} div_type_t;

/******************************************************************************\
  Datapath and control signal typedefs
\******************************************************************************/
typedef enum bit {
  pc_next   = 1'b0,
  pc_offset = 1'b1
} pc_mux_t;

typedef enum bit {
  rs1_out = 1'b0,
  pc_out  = 1'b1
} alu1_mux_t;

typedef enum bit {
  rs2_out = 1'b0,
  imm_out = 1'b1
} alu2_mux_t;

typedef enum bit [1:0] {
  id_source  = 2'b00,
  ex_source  = 2'b01,
  mem_source = 2'b10
} forward_mux_t;

typedef enum bit {
  rs2_cmp = 1'b0,
  imm_cmp = 1'b1
} cmp_mux_t;

typedef enum bit {
  pc_op  = 1'b0,
  rs1_op = 1'b1
} target_addr_mux_t;

typedef enum bit [2:0] {
  alu_out   = 3'b000,
  cmp_out   = 3'b001,
  addr_out  = 3'b010,
  mul_out   = 3'b011,
  div_out   = 3'b100
} func_mux_t;

typedef enum bit {
  mem_rdata_out = 1'b0,
  func_out      = 1'b1
} wb_mux_t;

/******************************************************************************\
  Pipeline stage typedefs
\******************************************************************************/

// Control signals
typedef struct packed {
  alu1_mux_t        alu1_mux;
  alu2_mux_t        alu2_mux;
  func_mux_t        func_mux;
  target_addr_mux_t target_addr_mux;
  logic             branch;
  logic             end_int;
  logic [2:0]       func_op;
  logic [2:0]       funct3;
} ex_ctrl_t;

typedef struct packed {
  logic       mem_write;
  logic       mem_read;
  logic [2:0] mem_funct3;
} mem_ctrl_t;

typedef struct packed {
  wb_mux_t     wb_mux;
  logic [2:0]  mem_funct3;
  logic        regf_we;
} wb_ctrl_t;

typedef struct packed {
  logic        valid;
  logic        int_valid;
  logic [63:0] order;
  logic [63:0] int_order;
  logic [31:0] inst;
  logic [4:0]  rs1_addr;
  logic [4:0]  rs2_addr;
  logic [31:0] rs1_rdata;
  logic [31:0] rs2_rdata;
  logic [4:0]  rd_addr;
  logic [31:0] rd_wdata;
  logic [31:0] pc_rdata;
  logic [31:0] pc_wdata;
  logic [31:0] mem_addr;
  logic [3:0]  mem_rmask;
  logic [3:0]  mem_wmask;
  logic [31:0] mem_rdata;
  logic [31:0] mem_wdata;
  logic        end_signal;
} rvfi_signal_t;

// Pipeline Stages
typedef struct packed {
  rvfi_signal_t rvfi;

  // Datapath Signals
  logic [31:0] pc;
  logic [31:0] pc_next;
  logic        int_flag;
} if_stage_t;

typedef struct packed {
  rvfi_signal_t rvfi;

  // Datapath Signals
  logic [31:0] pc;
  logic [31:0] pc_next;
  
  // Control Signals
  logic [4:0]  rs1_addr;
  logic [4:0]  rs2_addr;
  logic [4:0]  rd_addr;
  logic [31:0] imm;
  logic [31:0] rs1_rdata;
  logic [31:0] rs2_rdata;
  logic        int_flag;
  logic        end_int;
  ex_ctrl_t    ex_ctrl;
  mem_ctrl_t   mem_ctrl;
  wb_ctrl_t    wb_ctrl;
} id_stage_t;

typedef struct packed {
  rvfi_signal_t rvfi;

  // Datapath Signals
  logic [31:0] func_out;

  // Control Signals
  logic [4:0]  rd_addr;
  logic [31:0] rs2_rdata;
  mem_ctrl_t   mem_ctrl;
  wb_ctrl_t    wb_ctrl;
  logic        int_flag;
} ex_stage_t;

typedef struct packed {
  rvfi_signal_t rvfi;

  // Data Signals
  logic [31:0] func_out;

  // Control Signals
  logic [4:0]  rd_addr;
  mem_ctrl_t   mem_ctrl;
  wb_ctrl_t    wb_ctrl;
  logic        int_flag;
} mem_stage_t;

typedef struct packed {
  rvfi_signal_t rvfi;
} wb_stage_t;

/******************************************************************************\
  Constrained random typedefs
\******************************************************************************/
typedef enum bit [6:0] {
  base         = 7'b0000000,
  variant      = 7'b0100000,
  mult_variant = 7'b0000001
} funct7_t;

// Various ways RISC-V instruction words can be interpreted.
// See page 104, Chapter 19 RV32/64G Instruction Set Listings
// of the RISC-V v2.2 spec.
typedef union packed {
  bit [31:0] word;

  struct packed {
    bit [11:0] i_imm;
    bit [4:0] rs1;
    bit [2:0] funct3;
    bit [4:0] rd;
    rv32im_inst_opcode_t opcode;
  } i_type;

  struct packed {
    bit [6:0] funct7;
    bit [4:0] rs2;
    bit [4:0] rs1;
    bit [2:0] funct3;
    bit [4:0] rd;
    rv32im_inst_opcode_t opcode;
  } r_type;

  struct packed {
    bit [11:5] imm_s_top;
    bit [4:0]  rs2;
    bit [4:0]  rs1;
    bit [2:0]  funct3;
    bit [4:0]  imm_s_bot;
    rv32im_inst_opcode_t opcode;
  } s_type;

  struct packed {
    bit [11:5] imm_b_top;
    bit [4:0]  rs2;
    bit [4:0]  rs1;
    bit [2:0]  funct3;
    bit [4:0]  imm_b_bot;
    rv32im_inst_opcode_t opcode;
  } b_type;

  struct packed {
    bit [31:12] imm;
    bit [4:0]  rd;
    rv32im_inst_opcode_t opcode;
  } j_type;

} instr_t;

endpackage : rv32imc_types
