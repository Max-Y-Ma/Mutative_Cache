package cache_types;
  parameter integer ICACHE_WAYS = 2;
  parameter integer ICACHE_SETS = 16;

  parameter integer DCACHE_WAYS = 2;
  parameter integer DCACHE_SETS = 16;

  parameter integer L2CACHE_WAYS = 4;
  parameter integer L2CACHE_SETS = 64;

  parameter integer NUM_CORES = 4;
  parameter integer NUM_CACHE = NUM_CORES * 2;

  parameter integer XLEN           = 32;
  parameter integer XLEN_BYTES     = XLEN / 8;
  parameter integer CACHELINE_SIZE = 8;
  parameter integer COHERENCE_BITS = 3;

  parameter integer NUM_SETS = 4;
  parameter integer INDEX_WIDTH = $clog2(NUM_SETS);
  parameter integer TAG_WIDTH   = XLEN - INDEX_WIDTH;

  typedef enum logic [2:0] {
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
  } cacheline_state_t;

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
    logic                       valid;
    logic [$clog2(NUM_CACHE):0] source;
    logic [XLEN-1:0]            addr;
    bus_tx_t                    bus_tx;
  } req_msg_t;

  typedef struct packed {
    logic                       valid;
    logic [$clog2(NUM_CACHE):0] destination; // Requestor Destination
    logic                       memory_flag; // Memory Destination Flag
    logic [XLEN-1:0]            addr;
    logic [CACHELINE_SIZE-1:0]  data;
    memory_msg_t                mmsg;
  } resp_msg_t;

endpackage : cache_types
