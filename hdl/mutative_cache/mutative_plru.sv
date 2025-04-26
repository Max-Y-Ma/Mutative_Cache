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
    logic [WAY_IDX_BITS-1:0] virtual_evict_way;
    logic [WAYS-1:0] virtual_evict_we;


    always_ff @(posedge clk)begin: plru_1 //TODO: FIX MAYBE MAKE $ OF THEM
        if(rst) begin
            for(int unsigned i = 0; i < SET_SIZE; i++) begin
                PLRU_bits[i] <= {(WAYS-1){1'b0}};
            end
        end
        else if(hit)begin
            if (setup == 2'b01) begin
                PLRU_bits[cache_address.set_index] <= hit_way;
            end
            else if (setup == 2'b10) begin
                case (hit_way)
                    2'd0: PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][2], 2'b00};
                    2'd1: PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][2], 2'b10};
                    2'd2: PLRU_bits[cache_address.set_index] <= {1'b0, PLRU_bits[cache_address.set_index][1], 1'b1};
                    2'd3: PLRU_bits[cache_address.set_index] <= {1'b1, PLRU_bits[cache_address.set_index][1], 1'b1};
                endcase
            end else if (setup == 2'b11) begin
                case (hit_way)
                    3'd0: PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][6:4], 1'b0, PLRU_bits[cache_address.set_index][2], 2'b00};
                    3'd1: PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][6:4], 1'b1, PLRU_bits[cache_address.set_index][2], 2'b00};
                    3'd2: PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][6:5], 1'b0, PLRU_bits[cache_address.set_index][3:2], 2'b10};
                    3'd3: PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][6:5], 1'b1, PLRU_bits[cache_address.set_index][3:2], 2'b10};
                    3'd4: PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][6], 1'b0, PLRU_bits[cache_address.set_index][4:3], 1'b0, PLRU_bits[cache_address.set_index][1], 1'b1};
                    3'd5: PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][6], 1'b1, PLRU_bits[cache_address.set_index][4:3], 1'b0, PLRU_bits[cache_address.set_index][1], 1'b1};
                    3'd6: PLRU_bits[cache_address.set_index] <= {1'b0, PLRU_bits[cache_address.set_index][5:3], 1'b1, PLRU_bits[cache_address.set_index][1], 1'b1};
                    3'd7: PLRU_bits[cache_address.set_index] <= {1'b1, PLRU_bits[cache_address.set_index][5:3], 1'b1, PLRU_bits[cache_address.set_index][1], 1'b1};
                endcase
            end
        end
    end
 
 

    always_comb begin : replacement_1 //TODO: MAKE 4 and FIX
        virtual_evict_way = '0;
        virtual_evict_we = '0;
        case (setup)
            2'b01: begin
                case (~PLRU_bits[cache_address.set_index]) 
                    1'b0: begin
                        virtual_evict_way = '0;
                        virtual_evict_we = 1 << virtual_evict_way;
                    end
                    1'b1: begin
                        virtual_evict_way = '1;
                        virtual_evict_we = 1 << virtual_evict_way;
                    end
                endcase
            end
            2'b10: begin
                casez (~PLRU_bits[cache_address.set_index])
                    3'b?00: begin
                        virtual_evict_we = 4'b0001;//replace way 0
                        virtual_evict_way = 2'b00;
                    end
                    3'b?10: begin
                        virtual_evict_we = 4'b0010;//replace way 1
                        virtual_evict_way = 2'b01;
                    end
                    3'b0?1: begin 
                        virtual_evict_we = 4'b0100;//replace way 2
                        virtual_evict_way = 2'b10;
                    end
                    3'b1?1: begin 
                        virtual_evict_we = 4'b1000;//replace way 3
                        virtual_evict_way = 2'b11;
                    end
                endcase
            end
            2'b11: begin
                casez (~PLRU_bits[cache_address.set_index])
                    7'b???0?00: begin
                        virtual_evict_way = '0;
                        virtual_evict_we = 1 << virtual_evict_way;
                    end
                    7'b???1?00: begin
                        virtual_evict_way = 3'b001;
                        virtual_evict_we = 1 << virtual_evict_way;
                    end
                    7'b??0??00: begin
                        virtual_evict_way = 3'b010;
                        virtual_evict_we = 1 << virtual_evict_way;
                    end
                    7'b??1??00: begin
                        virtual_evict_way = 3'b011;
                        virtual_evict_we = 1 << virtual_evict_way;
                    end
                    7'b?0??0?1: begin
                        virtual_evict_way = 3'b100;
                        virtual_evict_we = 1 << virtual_evict_way;
                    end
                    7'b?1??0?1: begin
                        virtual_evict_way = 3'b101;
                        virtual_evict_we = 1 << virtual_evict_way;
                    end
                    7'b0???1?1: begin
                        virtual_evict_way = 3'b110;
                        virtual_evict_we = 1 << virtual_evict_way;
                    end
                    7'b1???1?1: begin
                        virtual_evict_way = 3'b111;
                        virtual_evict_we = 1 << virtual_evict_way;
                    end
                endcase
            end
        endcase
    end

    always_comb begin //offsetting virtual eviction signals to actual location
        unique case (setup)
            2'b00: begin //dm
                evict_way =  cache_address.tag[2:0];
                evict_we = 1 << cache_address.tag[2:0];
            end
            2'b01: begin //2-way
                evict_way = WAY_IDX_BITS'(virtual_evict_way+ (2)*cache_address.tag[1:0]);
                evict_we = 1 << evict_way;
            end
            2'b10: begin //4-way
                evict_way =  WAY_IDX_BITS'(virtual_evict_way + (4)*cache_address.tag[0]);
                evict_we = 1 << evict_way;
            end
            2'b11: begin//8-way
                evict_way =  virtual_evict_way;
                evict_we = virtual_evict_we;
            end
            default: begin
            end
        endcase
    end


endmodule

