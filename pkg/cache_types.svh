package cache_types;
  typedef enum logic [2:0] {
    IDLE,
    FLUSH,
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

endpackage : cache_types