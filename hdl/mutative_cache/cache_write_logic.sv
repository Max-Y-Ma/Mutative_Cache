module cache_write_data_controller
import mutative_types::*;
(
    // Input signals
    input logic mem_write_cache,       // Memory writing to cache signal
    input logic write_from_cpu,        // CPU writing to cache signal
    input logic [WAYS-1:0] evict_we,   // Way enable signals for eviction
    input logic [255:0] dfp_rdata,      // Data from memory
    input logic [31:0] ufp_wdata_ff,   // Data from CPU (flop-flop)
    input logic [3:0] ufp_wmask_ff,    // Write mask from CPU (flop-flop)
    input logic [WAY_IDX_BITS-1:0] hit_way,
    
    // Cache address components
    input cache_address_t cache_address,
    
    // Output signals
    output logic [WAYS-1:0] way_we,            // Way enable for writing
    output logic [31:0] cache_data_wmask,      // Byte enable mask for cache data
    output logic [255:0] cache_wdata,           // Data to write to cache
    output logic dirty_en                      // Enable signal for dirty bit
);

    //32 bits each bit represents 8 bits of 256 so 4 bits high will be 32 bti mask
    always_comb begin :cache_write_data_logic
        cache_data_wmask = 32'h00000000;
        cache_wdata = 'x;
        dirty_en = 1'b0;
        if(mem_write_cache) begin //memory writing cache
            way_we = evict_we;
            cache_data_wmask = 32'hFFFFFFFF;
            cache_wdata = dfp_rdata;
            dirty_en = 1'b0;
        end
        else if(write_from_cpu) begin //cpu writing cache
            cache_data_wmask[4*cache_address.block_offset[4:2] +: 4] = ufp_wmask_ff; // 00100
            cache_wdata[cache_address.block_offset[4:2]*32 +: 32] = ufp_wdata_ff;
            way_we = 1 << hit_way;
            dirty_en = 1'b1;
        end
        else begin
            way_we = {WAYS{1'b0}};
            cache_data_wmask = 32'h00000000;
            cache_wdata = 'x;
            dirty_en = 1'b0;
        end
    end
    
endmodule