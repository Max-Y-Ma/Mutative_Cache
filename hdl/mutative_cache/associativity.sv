module associativity
import mutative_types::*;
(
    input  logic                         clk,
    input  logic                         rst,
    input  logic                         cache_wen,
    input  logic                         dirty_en,
    input  logic   [31:0]                ufp_addr_ff,
    input  logic [WAYS-1:0]              way_we,
    input  cache_address_t               cache_address,

    // Outputs
    output logic                         full_assoc_hit,
    output logic                         real_cache_full,
    output logic                         full_assoc_full,
    output logic                         valid_bit
);

    logic [FULL_TAG_BITS-1:0]       full_assoc_tag;
    full_assoc_t                    full_assoc_cache[SET_SIZE*WAYS];
    logic [FULL_ASSOC_BITS-1:0]     full_assoc_hit_idx;

    assign full_assoc_tag = ufp_addr_ff >> OFFSET_BITS;
    assign valid_bit = full_assoc_cache[full_assoc_hit_idx].valid;

    always_comb begin //comparator 
        full_assoc_hit_idx = '0;
        full_assoc_hit = 1'b0;
        for (int i=0; i < (SET_SIZE*WAYS); ++i) begin
            if(full_assoc_tag == full_assoc_cache[i].tag && full_assoc_cache[i].valid) begin
                full_assoc_hit = 1'b1;
                full_assoc_hit_idx = i;
                break;
            end
        end
    end

    always_ff @(posedge clk) begin
        if(rst) begin
            for(int i = 0; i < (SET_SIZE*WAYS); i++)
                full_assoc_cache[i] <= '0;
        end else if(cache_wen) begin
            full_assoc_cache[full_assoc_hit_idx].valid <= 1'b1;
            full_assoc_cache[full_assoc_hit_idx].dirty <= dirty_en;
            full_assoc_cache[full_assoc_hit_idx].tag <= full_assoc_tag;
        end
    end

    
    logic virt_valid_array[SET_SIZE][WAYS];
    always_ff @(posedge clk) begin
        if(rst) begin
            for(int i = 0; i < SET_SIZE; i++) begin
                for(int j = 0; j < WAYS; j++) begin
                    virt_valid_array[i][j] <= '0;
                end
            end
        end else if(cache_wen) begin
            for(int i = 0; i < WAYS; i++) begin
                if(way_we[i]) begin
                    virt_valid_array[cache_address.set_index][i] <= 1'b1;
                end
            end

        end
    end


    always_comb begin
        real_cache_full = 1'b1;
        full_assoc_full = 1'b1;
        for(int i = 0; i < SET_SIZE; i++) begin
            for(int j = 0; j < WAYS; j++) begin
                if(virt_valid_array[i][j] == 0) begin
                    real_cache_full = 1'b0;
                end
            end
        end
        for (int k=0; k<(SET_SIZE*WAYS); ++k) begin
            if(full_assoc_cache[k].valid == 0) begin
                full_assoc_full = 1'b0;
            end
        end
    end

endmodule