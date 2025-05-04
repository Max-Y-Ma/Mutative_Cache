package mutative_types;
    localparam CACHELINE_SIZE = 256;
    localparam BLOCKS = CACHELINE_SIZE/8;
    localparam OFFSET_BITS = $clog2(BLOCKS);
    localparam TOTAL_SIZE = (2**12)*8; //4KiB
    localparam WAYS = 8;
    localparam WAY_IDX_BITS = $clog2(WAYS);

    localparam SET_SIZE = TOTAL_SIZE/(CACHELINE_SIZE*WAYS);
    localparam SET_BITS = $clog2(SET_SIZE);

    localparam TAG_BITS = 32 - SET_BITS - OFFSET_BITS;

    localparam FULL_TAG_BITS = 32 - OFFSET_BITS;
    localparam FULL_ASSOC_BITS = $clog2(SET_SIZE*WAYS);

    typedef struct packed {
        logic                           valid;
        logic                           dirty;
        logic [TAG_BITS-1:0]            tag;
        logic [CACHELINE_SIZE-1:0]      data;
    } cache_output_t;

    typedef struct packed {
        logic [TAG_BITS-1:0]        tag;
        logic [SET_BITS-1:0]        set_index;
        logic [OFFSET_BITS-1:0]     block_offset;
    } cache_address_t;

    typedef struct packed {
        logic                           valid;
        logic                           dirty;
        logic [FULL_TAG_BITS-1:0]       tag;
    } full_assoc_t;

endpackage : mutative_types
