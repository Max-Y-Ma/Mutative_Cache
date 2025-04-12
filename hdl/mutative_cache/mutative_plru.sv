module mutative_plru #(
    parameters
) (
    input logic clk, rst,
    input logic [WAY_IDX_BITS-1:0] hit_way,
    input logic hit,
    input cache_address_t cache_address,
    input logic [2:0] setup,
    output logic [1:0] evict_way,
    output logic [WAYS-1:0] evict_we

);
    logic [WAYS-2:0] PLRU_bits[SET_SIZE]; 
    always_ff @(posedge clk)begin: plru_1 //TODO: FIX MAYBE MAKE $ OF THEM
        if(rst) begin
            for(int unsigned i = 0; i < SET_SIZE; i++) begin
                PLRU_bits[i] <= {(WAYS-1){1'b0}};
            end
        end
        else if(hit)begin
            for(int i = 0; i < WAYS; i++) begin
                //if()
                if(hit_way == i) 
                    PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][2], 2'b00};
            end

            while (expression) begin
                
            end


            // unique case (hit_way)
            //     2'd0: PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][2], 2'b00};
            //     2'd1: PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][2], 2'b10};
            //     2'd2: PLRU_bits[cache_address.set_index] <= {1'b0, PLRU_bits[cache_address.set_index][1], 1'b1};
            //     2'd3: PLRU_bits[cache_address.set_index] <= {1'b1, PLRU_bits[cache_address.set_index][1], 1'b1};
            // endcase
        end
    end

    logic [1:0] evict_way;
    always_comb begin : replacement_1 //TODO: MAKE 4 and FIX
        casez (~PLRU_bits[cache_address.set_index])
            3'b?00: begin
                evict_we = 4'b0001;//replace way 0
                evict_way = 2'b00;
            end
            3'b?10: begin
                evict_we = 4'b0010;//replace way 1
                evict_way = 2'b01;
            end
            3'b0?1: begin 
                evict_we = 4'b0100;//replace way 2
                evict_way = 2'b10;
            end
            3'b1?1: begin 
                evict_we = 4'b1000;//replace way 3
                evict_way = 2'b11;
            end
        endcase
    end


endmodule