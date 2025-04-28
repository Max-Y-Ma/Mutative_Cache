package cache_types;
  parameter integer ICACHE_WAYS = 2;
  parameter integer ICACHE_SETS = 16;

  parameter integer DCACHE_WAYS = 2;
  parameter integer DCACHE_SETS = 16;

  parameter integer L2CACHE_WAYS = 4;
  parameter integer L2CACHE_SETS = 64;

  parameter integer NUM_CORES = 1;
  parameter integer NUM_CACHE = NUM_CORES * 2;

  parameter integer XLEN           = 32;
  parameter integer XLEN_BYTES     = XLEN / 8;
  parameter integer CACHELINE_SIZE = 256;
  parameter integer COHERENCE_BITS = 3;

  typedef enum logic [COHERENCE_BITS-1:0] {
    IDLE,
    CHECK,
    WRITEBACK,
    FETCH,
    FETCH_WAIT
  } controller_state_t;

  typedef enum logic [2:0] {
    LINE_IDLE,
    WAIT,
    SERIALIZE,
    DESERIALIZE,
    DESERIALIZE_DONE
  } line_buffer_state_t;

  typedef enum logic [1:0] {
    CPU_READ,
    CPU_WRITE,
    CPU_IDLE
  } cpu_state_t;

  typedef enum logic [1:0] {
    GETS, // Shared State Request
    GETM, // Modified State Request
    PUTM, // Block Eviction
    NONE  // No Request
  } bus_tx_t;

  typedef enum logic [3:0] {
    CI,    // Invalid
    CISAD, // Invalid -> Shared Request Wait
    CISD,  // Invalid -> Shared Response Wait
    CIMAD, // Invalid -> Modified Request Wait
    CIMD,  // Invalid -> Modified Response Wait
    CIRD,  // Exclusive, Modified -> Invalid Data Request Wait
    CS,    // Shared
    CSMAD, // Shared -> Modified Request Wait
    CSMD,  // Shared -> Modified Response Wait
    CSRD,  // Exclusive, Modified -> Shared Data Request Wait
    CE,    // Exclusive
    CM,    // Modified
    CMIA,  // Modified -> Invalid Request Wait
    CEIA,  // Exclusive -> Invalid Request Wait
    CIIA,  // Invalid Request Wait
    CIIARD // Exclusive, Modified -> IIA Data Request Wait
  } cacheline_state_t;

  typedef enum logic [COHERENCE_BITS-1:0] {
    MI,      // Invalid
    MS,      // Shared
    MSRD,    // Shared Wait State
    MEORM,   // Exclusive or Modified
    MEORMRD, // Exclusive or Modified Wait State
    MID,     // Invalid Delay
    MSD,     // Shared Delay
    MEORMD   // Exclusive or Modified Delay
  } llc_memory_state_t;

  typedef enum logic [1:0] {
    EXCLUSIVE, // Message Contains Exclusive Data
    DATA,      // Message Contains Valid Data
    NODATA,    // Message Contains No Data
    NODATAE    // Message Contains No Data Exclusive
  } memory_msg_t;

  typedef struct packed {
    logic                       valid;
    logic [$clog2(NUM_CACHE):0] source;
    logic [XLEN-1:0]            addr;
    bus_tx_t                    bus_tx;
  } req_msg_t;

  typedef struct packed {
    logic                            valid;
    logic [$clog2(NUM_CACHE):0]      source;
    logic [$clog2(L2CACHE_WAYS)-1:0] way;
    logic [$clog2(NUM_CACHE):0]      destination; // Requestor Destination
    logic                            memory_flag; // Memory Destination Flag
    logic [XLEN-1:0]                 addr;
    logic [CACHELINE_SIZE-1:0]       data;
    memory_msg_t                     mmsg;
  } resp_msg_t;

endpackage : cache_types
