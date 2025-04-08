package adp_types;

  localparam ACADIA_DEVICE_ID = 32'h69ECE498;

  localparam NUM_BOUNDARY_CELLS = 49;

  /**
   * Debug Memory Map, the address space is 16-bits wide.
   *
   * The address assignment is designed to reduce decoding complexity. The
   * address space is broken down into four sections: Data SRAM, Core Registers,
   * Core Data, and Peripheral Data. The upper four MSBs indicate the section
   * using a one-hot encoding. The offset is given by the lowest 12-bits.
   * Thus, 32K addresses can be selected.  
   */ 
  localparam SRAM_ADDR_START = 'h2000;
  localparam SRAM_ADDR_END   = 'h3FFF;
  localparam SRAM_ADDR_BIT   = 'd13;
  localparam SRAM_ADDR_WIDTH = 'd13;

  localparam REG_ADDR_START  = 'h4000; 
  localparam REG_ADDR_END    = 'h401F;
  localparam REG_ADDR_BIT    = 'd14;
  localparam REG_ADDR_WIDTH  = 'd5;

  localparam CORE_ADDR_START = 'h8000;
  localparam CORE_PC_ADDR    = 2'h0;
  localparam CORE_IR_ADDR    = 2'h1;
  localparam CORE_ADC_ADDR   = 2'h2;
  localparam CORE_DAC_ADDR   = 2'h3; 
  localparam CORE_ADDR_END   = 'h8003;
  localparam CORE_ADDR_BIT   = 'd15;
  localparam CORE_ADDR_WIDTH = 'd2;

  localparam RESET_CYCLES    = 6;

  typedef enum bit [2:0] {
    NULL_MODE       = 3'b000,
    DEVICE_ID_READ  = 3'b001,
    SCAN_MODE       = 3'b010,
    BOUNDARY_SCAN   = 3'b011,
    BYPASS_MODE     = 3'b100,
    DEBUG_READ      = 3'b101,
    DEBUG_WRITE     = 3'b110,
    STEP_MODE       = 3'b111
  } adp_instruction_t;

  typedef struct packed {
    logic             imem_stall;
    logic             dmem_stall;
    logic             func_stall;
    logic             load_hazard;
    adp_instruction_t inst;
  } inst_reg_t;
    
  typedef enum bit [2:0] {
    NULL       = 3'b000,
    DEVICE_ID  = 3'b001,
    SCAN_CHAIN = 3'b010,
    BYPASS     = 3'b011,
    BOUNDARY   = 3'b100,
    DATA_REG   = 3'b101
  } tdo_mux_sel_t;

  typedef enum bit [3:0] {
    IDLE,
    DR_SCAN,
    DR_JUMP,
    DR_SETUP,
    EX_SHIFT,
    EX_UPDATE,
    IN_CAPTURE,
    IN_SHIFT,
    SR_SCAN,
    SR_SHIFT,
    IR_SCAN,
    IR_CAPTURE,
    IR_SHIFT,
    AR_SCAN,
    AR_SHIFT,
    PAUSE
  } tap_state_t;

endpackage : adp_types