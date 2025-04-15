module mutative_plru
import mutative_types::*;
(
    input logic clk, rst,
    input logic [WAY_IDX_BITS-1:0] hit_way,
    input logic hit,
    input cache_address_t cache_address,
    input logic [1:0] setup,
    output logic [WAY_IDX_BITS-1:0] evict_way,
    output logic [WAYS-1:0] evict_we

);
    logic [WAYS-2:0] PLRU_bits[SET_SIZE]; 
    logic [WAYS-2:0] PLRU_bits_next;
    logic [WAYS-2:0] PLRU_update_mask;
    logic [WAY_IDX_BITS-1:0] hit_way_inv;
    assign hit_way_inv = ~hit_way;


    always_comb begin
        PLRU_bits_next    = '0;
        PLRU_update_mask  = '0;

        if (hit) begin
            // Update bit 0
            PLRU_bits_next[0] = hit_way_inv[WAY_IDX_BITS-1];
            PLRU_update_mask |= (1 << 0);

            if (setup != 2'b0 && setup != 2'b01) begin  // >2-way cache
                if (PLRU_bits_next[0] == 0) begin
                    PLRU_bits_next[1] = hit_way_inv[WAY_IDX_BITS-2];
                    PLRU_update_mask |= (1 << 1);
                end else begin
                    PLRU_bits_next[2] = hit_way_inv[WAY_IDX_BITS-2];
                    PLRU_update_mask |= (1 << 2);
                end

                if (setup != 2'b10) begin  // >4-way cache
                    if (PLRU_bits_next[0] == 0) begin
                        if (PLRU_bits_next[1] == 0) begin
                            PLRU_bits_next[3] = hit_way_inv[WAY_IDX_BITS-3];
                            PLRU_update_mask |= (1 << 3);
                        end else begin
                            PLRU_bits_next[4] = hit_way_inv[WAY_IDX_BITS-3];
                            PLRU_update_mask |= (1 << 4);
                        end
                    end else begin
                        if (PLRU_bits_next[2] == 0) begin
                            PLRU_bits_next[5] = hit_way_inv[WAY_IDX_BITS-3];
                            PLRU_update_mask |= (1 << 5);
                        end else begin
                            PLRU_bits_next[6] = hit_way_inv[WAY_IDX_BITS-3];
                            PLRU_update_mask |= (1 << 6);
                        end
                    end
                end
            end
        end
    end 

    /*always_comb begin
        PLRU_bits_next = '0;
        PLRU_update_mask = '0;

        if (hit) begin
            int bit_index = 0;
            int offset = 0;

            for (int level = 0; level < WAY_IDX_BITS; level++) begin
                bit PLRU_bit_value = hit_way_inv[WAY_IDX_BITS-1-level]; // which direction to go at this level

                PLRU_bits_next[bit_index] = PLRU_bit_value; // update the bit in the PLRU tree
                PLRU_update_mask |= (1 << bit_index);

                if (PLRU_bit_value == 0)
                    bit_index = bit_index*2+1;  // go left down the tree
                else
                    bit_index = bit_index*2+2;  // go right down the tree
            end
        end
    end */



    always_ff @(posedge clk)begin: plru_1 
        if(rst) begin
            for(int unsigned i = 0; i < SET_SIZE; i++) begin
                PLRU_bits[i] <= {(WAYS-1){1'b0}};
            end
        end
        else if(hit)begin
            PLRU_bits[cache_address.set_index] <= (PLRU_bits[cache_address.set_index] & ~PLRU_update_mask) | (PLRU_bits_next & PLRU_update_mask);

            /*for(int i = 0; i < WAYS; i++) begin
                if(hit_way == i) begin
                    PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][2], 2'b00};
                end
            end

            unique case (hit_way)
                2'd0: PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][2], 2'b00};
                2'd1: PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][2], 2'b10};
                2'd2: PLRU_bits[cache_address.set_index] <= {1'b0, PLRU_bits[cache_address.set_index][1], 1'b1};
                2'd3: PLRU_bits[cache_address.set_index] <= {1'b1, PLRU_bits[cache_address.set_index][1], 1'b1};
            endcase*/
        end
    end

    always_comb begin
        evict_way = '0;
        evict_we  = '0;

        if (setup == 2'b01) begin // 2-way
            evict_way = PLRU_bits[cache_address.set_index][0];
        end else if (setup != 2'b00 && setup != 2'b01) begin // > 2-way
            if (PLRU_bits[cache_address.set_index][0] == 0) begin
                if (setup == 2'b10) begin // 4-way
                    evict_way = {1'b0, PLRU_bits[cache_address.set_index][1]};
                end else begin //8-way
                    if (PLRU_bits[cache_address.set_index][1] == 0) begin
                        evict_way = {2'b00, PLRU_bits[cache_address.set_index][3]};
                    end else begin
                        evict_way = {2'b01, PLRU_bits[cache_address.set_index][4]};
                    end
                end
            end else begin // pleubit0 == 1
                if (setup == 2'b10) begin // 4-way
                    evict_way = {1'b1, PLRU_bits[cache_address.set_index][2]};
                end else begin // 8-way
                    if (PLRU_bits[cache_address.set_index][2] == 0) begin
                        evict_way = {2'b10, PLRU_bits[cache_address.set_index][5]};
                    end else begin
                        evict_way = {2'b11, PLRU_bits[cache_address.set_index][6]};
                    end
                end
            end
        end

        evict_we = 1 << evict_way;
    end


    /*always_comb begin : replacement_1 

        int bit_index = 0;
        evict_way = '0;
        evict_we = '0;

        for (int level = 0; level < WAY_IDX_BITS; level++) begin
            logic direction = PLRU_bits[cache_address.set_index][bit_index]; //determine direction to traverse down the tree
            
            evict_way[WAY_IDX_BITS-1-level] = direction;

            if (direction == 0)
                bit_index = bit_index*2 + 1;  // go left down the tree
            else
                bit_index = bit_index*2 + 2;  // go right down the tree

        end

        evict_we = 1 << evict_way;
    end */


endmodule

