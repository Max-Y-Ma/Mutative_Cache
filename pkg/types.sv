package types;

  parameter integer NUM_CPUS = 4;
  parameter integer NUM_SETS = 4;

  parameter integer XLEN           = 6;
  parameter integer CACHELINE_SIZE = 8;
  parameter integer COHERENCE_BITS = 3;

  parameter integer INDEX_WIDTH = $clog2(NUM_SETS);
  parameter integer TAG_WIDTH   = XLEN - INDEX_WIDTH;

  typedef enum {
    CPU_READ,
    CPU_WRITE,
    CPU_IDLE
  } cpu_state_t;

  typedef enum {
    GETS, // Shared State Request
    GETM, // Modified State Request
    PUTM, // Block Eviction
    IDLE  // No Request
  } bus_tx_t;

  typedef enum {
    CI,    // Invalid
    CISAD, // Invalid -> Shared Request Wait
    CISD,  // Invalid -> Shared Response Wait
    CIMAD, // Invalid -> Modified Request Wait
    CIMD,  // Invalid -> Modified Response Wait
    CS,    // Shared
    CSMAD, // Shared -> Modified Request Wait
    CSMD,  // Shared -> Modified Response Waait
    CE,    // Exclusive
    CM,    // Modified
    CMIA,  // Modified -> Invalid Request Wait
    CEIA,  // Exclusive -> Invalid Request Wait
    CIIA   // Invalid Request Wait
  } cacheline_state_t;

  typedef enum logic [COHERENCE_BITS-1:0] {
    MI,    // Invalid
    MS,    // Shared
    MEORM, // Exclusive or Modified
    MID,   // Invalid Delay
    MSD,   // Shared Delay
    MEORMD // Exclusive or Modified Delay
  } memory_state_t;

  typedef enum {
    EXCLUSIVE, // Message Contains Exclusive Data
    DATA,      // Message Contains Valid Data
    NODATA,    // Message Contains No Data
    NODATAE    // Message Contains No Data Exclusive
  } memory_msg_t;

  typedef struct packed {
    cacheline_state_t          state;
    logic [CACHELINE_SIZE-1:0] data;
    logic [TAG_WIDTH-1:0]      tag;
  } cacheline_t;

  typedef struct packed {
    logic                      valid;
    logic [$clog2(NUM_CPUS):0] source;
    logic [XLEN-1:0]           addr;
    bus_tx_t                   bus_tx;
  } bus_msg_t;

  typedef struct packed {
    logic                      valid;
    logic [$clog2(NUM_CPUS):0] destination; // Requestor Destination
    logic                      memory_flag; // Memory Destination Flag
    logic [XLEN-1:0]           addr;
    logic [CACHELINE_SIZE-1:0] data;
    memory_msg_t               mmsg;
  } xbar_msg_t;

endpackage
