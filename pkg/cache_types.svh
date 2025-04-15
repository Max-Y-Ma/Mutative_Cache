// package cache_types;

//   typedef enum bit [2:0] {
//     IDLE,           // Initial state
//     CHECK,          // Central check state
//     FETCH,          // Single cacheline fetch state
//     FETCH_WAIT,     // Single cacheline fetch wait state
//     CHECK_SECOND,   // Second cacheline central check state
//     FETCH_FIRST,    // Second cacheline first fetch state
//     FETCH_SECOND,   // Second cacheline second fetch state
//     WAIT_SECOND     // Second cacheline second fetch wait state
//   } icontroller_state_t;

//   typedef enum bit [2:0] {
//     DIDLE,
//     DCHECK,
//     DFETCH,
//     DWRITEBACK, 
//     DFETCH_WAIT
//   } dcontroller_state_t;

//   typedef enum bit [2:0] {
//     LINE_IDLE,
//     WAIT,
//     SERIALIZE,
//     DESERIALIZE
//   } cacheline_state_t;

// endpackage : cache_types

package cache_types;
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
endpackage;