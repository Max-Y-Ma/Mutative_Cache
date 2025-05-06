module mutative_plru
import mutative_types::*;
(
    input logic clk, rst,
    input logic [WAY_IDX_BITS-1:0] hit_way,
    input logic hit,
    input cache_address_t cache_address,
    input logic [1:0] setup,
    output logic [WAY_IDX_BITS-1:0] evict_way,
    output logic [WAYS-1:0] evict_we,
    output logic left_or_right,
    output logic tie
);

    logic [2:0] dm_way_index;
    logic [2:0] two_way_index;
    logic [2:0] four_way_index;

    logic [WAYS-1:0] plru_bits[SET_SIZE];

    assign dm_way_index = cache_address.tag[2:0]  << 0; //0-8 *1
    assign two_way_index = cache_address.tag[2:1] << 1; //0-3 *2
    assign four_way_index = cache_address.tag[2]  << 2; // 0 or 1 *4

    logic almost_full;
    logic[3:0] zero_count;
    assign almost_full = (zero_count == 1);

    always_comb begin // only one 0 left
        zero_count = 0;
        unique case (setup)
            2'b00: begin //dm

            end
            2'b01: begin //2-way
                for (int i=0; i<2; ++i) begin
                    if(plru_bits[cache_address.set_index][i + two_way_index] == 0) begin
                        zero_count++;
                    end
                end
            end
            2'b10: begin //4-way
                for (int i=0; i<4; ++i) begin
                    if(plru_bits[cache_address.set_index][i + four_way_index] == 0) begin
                        zero_count++;
                    end
                end
            end
            2'b11: begin//8-way
                for (int i=0; i<8; ++i) begin
                    if(plru_bits[cache_address.set_index][i] == 0) begin
                        zero_count++;
                    end
                end
            end
            default: begin
            end
        endcase
    end

    always_ff @(posedge clk) begin // update plru logic
        if(rst) begin
            for(int i = 0; i < SET_SIZE; i++) begin
                plru_bits[i] <= '0;
            end
        end else if (hit) begin
            unique case (setup)
                2'b00: begin //dm

                end
                2'b01: begin //2-way
                    if( (plru_bits[cache_address.set_index][hit_way] == 1'b0) && almost_full) begin //reset
                        plru_bits[cache_address.set_index][two_way_index+:2] <= 2'd0;
                        plru_bits[cache_address.set_index][hit_way] <= 1'b1;
                    end else if((plru_bits[cache_address.set_index][hit_way] == 1'b0))begin
                        plru_bits[cache_address.set_index][hit_way] <= 1'b1;
                    end
                end
                2'b10: begin //4-way
                    if( (plru_bits[cache_address.set_index][hit_way] == 1'b0) && almost_full) begin //reset
                        plru_bits[cache_address.set_index][four_way_index+:4] <= 4'd0;
                        plru_bits[cache_address.set_index][hit_way] <= 1'b1;
                    end else if((plru_bits[cache_address.set_index][hit_way] == 1'b0))begin
                        plru_bits[cache_address.set_index][hit_way] <= 1'b1;
                    end
                end
                2'b11: begin//8-way
                    if( (plru_bits[cache_address.set_index][hit_way] == 1'b0) && almost_full) begin //reset
                        plru_bits[cache_address.set_index] <= '0;
                        plru_bits[cache_address.set_index][hit_way] <= 1'b1;
                    end else if((plru_bits[cache_address.set_index][hit_way] == 1'b0))begin
                        plru_bits[cache_address.set_index][hit_way] <= 1'b1;
                    end
                end
                default: begin
                end
            endcase
        end
    end

    always_comb begin
        unique case (setup)
            2'b00: begin //dm
                evict_way = dm_way_index;
                evict_we = 1 << evict_way;
            end
            2'b01: begin //2-way
                for (int i=0; i<2; ++i) begin
                    if(plru_bits[cache_address.set_index][i + two_way_index] == 0) begin
                        evict_way = i + two_way_index;
                        break;
                    end
                end
                evict_we = 1 << evict_way;
            end
            2'b10: begin //4-way
                for (int i=0; i<4; ++i) begin
                    if(plru_bits[cache_address.set_index][i + four_way_index] == 0) begin
                        evict_way = i + four_way_index;
                        break;
                    end
                end
                evict_we = 1 << evict_way;
            end
            2'b11: begin//8-way
                for (int i=0; i<8; ++i) begin
                    if(plru_bits[cache_address.set_index][i] == 0) begin
                        evict_way = i;
                        break;
                    end
                end
                evict_we = 1 << evict_way;
            end
            default: begin
            end
        endcase
    end

    logic [2:0] left_counter;
    logic [2:0] right_counter;

    assign left_or_right = (left_counter < right_counter); //left > right: 0, left < right: 1
    assign tie = (left_counter == right_counter);

    always_comb begin
        left_counter = '0;
        right_counter = '0;
        unique case (setup)
            2'b01: begin //2-way
                for (int i=0; i<2; ++i) begin
                    if(plru_bits[cache_address.set_index][i + two_way_index] == 1 && i == 0) begin
                        left_counter++;
                    end else if (plru_bits[cache_address.set_index][i + two_way_index] == 1 && i == 1) begin
                        right_counter++;
                    end
                end
            end
            2'b10: begin //4-way
                for (int i=0; i<4; ++i) begin
                    if(plru_bits[cache_address.set_index][i + four_way_index] == 1 && i < 2) begin //[0-3][4-7]
                        left_counter++;
                    end else if(plru_bits[cache_address.set_index][i] == 1 && i >= 2) begin
                        right_counter++;
                    end
                end
            end
            2'b11: begin//8-way
                for (int i=0; i<8; ++i) begin
                    if(plru_bits[cache_address.set_index][i] == 1 && i < 4) begin
                        left_counter++;
                    end else if(plru_bits[cache_address.set_index][i] == 1 && i >= 4) begin
                        right_counter++;
                    end
                end
            end
            default: begin
            end
        endcase
    end



endmodule

