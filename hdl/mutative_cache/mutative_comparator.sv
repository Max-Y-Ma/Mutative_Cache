module mutative_comparator
import mutative_types::*;
(
    input cache_address_t           cache_address,
    input cache_output_t            cache_output [WAYS],
    input logic [1:0]               setup,
    input logic [3:0]               ufp_rmask_ff,
    input logic                     ufp_resp,

    output logic [WAY_IDX_BITS-1:0] hit_way,
    output logic                    true_csb0[WAYS-1:0],
    output logic                    hit,
    output logic [31:0]             ufp_rdata

);

    logic [WAYS-1:0] compare_result;
    logic [31:0] true_data;
    logic [2:0] dm_way_index;
    logic [2:0] two_way_index;
    logic [2:0] four_way_index;
    always_comb begin: comparator_1
        hit_way = {WAY_IDX_BITS{1'b0}};
        compare_result = {WAYS{1'b0}};
        dm_way_index = cache_address.tag[2:0]  << 0; //0-8
        two_way_index = cache_address.tag[1:0] << 1; //0-3
        four_way_index = cache_address.tag[0]  << 2; // 0 or 1
        for (int i=0; i<WAYS; ++i)
            true_csb0[i] = 1'b1;
        if(setup == 0) begin //DM
            true_csb0[dm_way_index] = 1'b0;
            if(cache_output[dm_way_index].valid&&(cache_output[dm_way_index].tag[TAG_BITS-4:0] == cache_address.tag[TAG_BITS-4:0])) begin
                compare_result[dm_way_index] = 1'b1;
                hit_way = WAY_IDX_BITS'(dm_way_index);
            end
        end else if(setup == 1) begin //2-way
            for (int unsigned i = 0; i < 2; i++) begin
                true_csb0[i+ two_way_index] = 1'b0;
                if(cache_output[i+ two_way_index].valid&&(cache_output[i+ two_way_index].tag[TAG_BITS-3:0] == cache_address.tag[TAG_BITS-3:0])) begin
                    compare_result[i+ two_way_index] = 1'b1;
                    hit_way = WAY_IDX_BITS'(i+ two_way_index);
                end
            end
        end else if(setup == 2) begin //4-way
            for (int unsigned i = 0; i < 4; i++) begin
                true_csb0[i+ four_way_index] = 1'b0;
                if(cache_output[i+ four_way_index].valid&&(cache_output[i+ four_way_index].tag[TAG_BITS-2:0] == cache_address.tag[TAG_BITS-2:0])) begin
                    compare_result[i+ four_way_index] = 1'b1;
                    hit_way = WAY_IDX_BITS'(i+ four_way_index);
                end
            end
        end else begin //8-way
            for (int unsigned i = 0; i < WAYS; i++) begin
                true_csb0[i] = 1'b0;
                if(cache_output[i].valid&&(cache_output[i].tag[TAG_BITS-1:0] == cache_address.tag)) begin
                    compare_result[i] = 1'b1;
                    hit_way = WAY_IDX_BITS'(i);
                end
            end
        end
        true_data = cache_output[hit_way].data[cache_address.block_offset[4:2]*32 +: 32];
        hit = |compare_result;
        ufp_rdata = (ufp_resp && |ufp_rmask_ff)? true_data : 'x;
    end

endmodule
