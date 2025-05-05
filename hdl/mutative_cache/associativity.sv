module associativity
import mutative_types::*;
(
    input  logic                         clk,
    input  logic                         rst,
    input  cache_address_t               cache_address,
    input  logic                         cpu_req,
    input  logic                         cache_ready,
    input  logic                         setup_ready,
    input  logic [1:0]                   setup,
    input  logic                         plru_bit0,

    output logic                         switch_dir,
    output logic                         switch_valid
);

    logic setup_ready_read;

    logic switched;

    logic [16:0] total_accesses;
    logic [16:0] total_accesses_next;

    logic [1:0] dead_set_counter [0:(WAYS*SET_SIZE)-1];
    logic [3:0] stack_distance [0:((WAYS*SET_SIZE)/2)-1];
    logic [1:0] dead_set_counter_next [0:(WAYS*SET_SIZE)-1];
    logic [3:0] stack_distance_next [0:((WAYS*SET_SIZE)/2)-1];

    logic [7:0] total_dead_sets;
    logic [7:0] total_saturated_sets;
    logic [7:0] total_dead_sets_next;
    logic [7:0] total_saturated_sets_next;

    logic [2:0] dm_way_index; 
    logic [1:0] two_way_index; 
    logic       four_way_index;
    logic [6:0] true_set_index;

    assign dm_way_index = cache_address.tag[2:0];
    assign two_way_index = cache_address.tag[1:0];
    assign four_way_index = cache_address.tag[0] ;


    enum logic [2:0] {
    a_ready, a_wait, a_switch, a_switch_decision, a_switch_wait
    } a_state, a_next_state;

    always_ff @(posedge clk) begin
        switched <= switch_valid;
        setup_ready_read <= setup_ready;
    end

    always_comb begin
        case (setup)
            2'b00: true_set_index = cache_address.set_index + dm_way_index;
            2'b01: true_set_index = cache_address.set_index + two_way_index;
            2'b10: true_set_index = cache_address.set_index + four_way_index;
            2'b11: true_set_index = cache_address.set_index;
        endcase
    end

    

    always_comb begin
        dead_set_counter_next = dead_set_counter;
        stack_distance_next = stack_distance;
        total_accesses_next = total_accesses;
        total_saturated_sets_next = total_saturated_sets;
        total_dead_sets_next = total_dead_sets;
        if (rst) begin
            for (int i = 0; i < 128; i++) begin
                dead_set_counter_next[i] = 2'b00;
                stack_distance_next[i] = 4'd7;
                total_accesses_next = '0;
                total_dead_sets_next = '0;
                total_saturated_sets_next = '0;
            end
        end else begin
            case (a_state)
                a_ready: begin
                    if (cpu_req) begin
                        if (dead_set_counter[true_set_index] < 2'b11)
                            dead_set_counter_next[true_set_index] = dead_set_counter[true_set_index] + 1'b1;
                        if (setup != '0) begin
                            if (plru_bit0 == '0) begin
                                if (stack_distance[true_set_index] > '0)
                                    stack_distance_next[true_set_index] = stack_distance[true_set_index] - 1'b1;
                            end else begin
                                if (stack_distance[true_set_index] < 4'b1111)
                                    stack_distance_next[true_set_index] = stack_distance[true_set_index] + 1'b1;
                            end
                        end
                        total_accesses_next = total_accesses_next + 1'b1;
                    end  
                end
                a_switch: begin
                    case (setup)
                        2'b00: begin
                            for (int i = 0; i < 128; i++) begin
                                if (dead_set_counter[i] != 2'b11) begin
                                    
                                    total_dead_sets_next = total_dead_sets_next + 1'b1;
                                    $display("Incremented: total_dead_sets_next = %0d", total_dead_sets_next);
                                end
                            end
                        end 
                        2'b01: begin
                            for (int i = 0; i < 64; i++) begin
                                if (dead_set_counter[i] != 2'b11) 
                                    total_dead_sets_next = total_dead_sets_next + 1'b1;
                                if (stack_distance[i] == 4'b0000 || stack_distance[i] == 4'b0001 || stack_distance[i] == 4'b1110 || stack_distance[i] == 4'b1111)
                                    total_saturated_sets_next =total_saturated_sets_next + 1'b1;
                            end
                        end 
                        2'b10: begin
                            for (int i = 0; i < 32; i++) begin
                                if (dead_set_counter[i] != 2'b11) 
                                    total_dead_sets_next = total_dead_sets_next + 1'b1;
                                if (stack_distance[i] == 4'b0000 || stack_distance[i] == 4'b0001 || stack_distance[i] == 4'b1110 || stack_distance[i] == 4'b1111)
                                    total_saturated_sets_next =total_saturated_sets_next + 1'b1;
                            end
                        end
                        2'b11: begin
                            for (int i = 0; i < 16; i++) begin
                                if (dead_set_counter[i] != 2'b11) 
                                    total_dead_sets_next = total_dead_sets_next + 1'b1;
                                if (stack_distance[i] == 4'b0000 || stack_distance[i] == 4'b0001 || stack_distance[i] == 4'b1110 || stack_distance[i] == 4'b1111)
                                    total_saturated_sets_next = total_saturated_sets_next + 1'b1;
                            end
                        end
                    endcase
                end
                a_switch_decision: begin
                    switch_valid = '0;
                    case (setup)
                        2'b00: begin
                            if (total_dead_sets >= 82) begin
                                switch_dir = '1;
                                switch_valid = '1;
                            end
                        end 
                        2'b01: begin
                            if (total_dead_sets >= 43 && total_saturated_sets <= 22) begin
                                switch_dir = '1;
                                switch_valid = '1;
                            end else if (total_saturated_sets >= 43 && total_dead_sets <= 22) begin
                                switch_dir = '0;
                                switch_valid = '1;
                            end
                        end 
                        2'b10: begin
                            if (total_dead_sets >= 21 && total_saturated_sets <= 11) begin
                                switch_dir = '1;
                                switch_valid = '1;
                            end else if (total_saturated_sets >= 22 && total_dead_sets <= 11) begin
                                switch_dir = '0;
                                switch_valid = '1;
                            end
                        end
                        2'b11: begin
                            if (total_dead_sets >= 11 && total_saturated_sets <= 5) begin
                                switch_dir = '1;
                                switch_valid = '1;
                            end else if (total_saturated_sets >= 11 && total_dead_sets <= 5) begin
                                switch_dir = '0;
                                switch_valid = '1;
                            end
                        end
                    endcase
                end
                a_switch_wait: begin
                    if (!switched) begin
                        for (int i = 0; i < 128; i++) begin
                            dead_set_counter_next[i] = 2'b00;
                            stack_distance_next[i] = 4'd7;
                            total_accesses_next = '0;
                            total_dead_sets_next = '0;
                            total_saturated_sets_next = '0;
                        end
                    end
                    else if (setup_ready_read) begin
                        switch_valid = '0;
                        for (int i = 0; i < 128; i++) begin
                            dead_set_counter_next[i] = 2'b00;
                            stack_distance_next[i] = 4'd7;
                            total_accesses_next = '0;
                            total_dead_sets_next = '0;
                            total_saturated_sets_next = '0;
                        end
                    end
                end
            endcase
        end
    end

    always_ff @(posedge clk) begin
        dead_set_counter <= dead_set_counter_next;
        stack_distance <= stack_distance_next;
        total_accesses <= total_accesses_next;
        total_saturated_sets <= total_saturated_sets_next;
        total_dead_sets <= total_dead_sets_next;
    end

    always_comb begin //next_state logic
        a_next_state = a_state;
        case (a_state)
            a_ready: begin
                if (total_accesses >= 17'd10000) 
                    a_next_state = a_switch;
                else if (cpu_req)
                    a_next_state = a_wait;
            end
            a_switch: begin
                a_next_state = a_switch_decision;
            end
            a_switch_decision: begin
                a_next_state = a_switch_wait;
            end
            a_switch_wait: begin
                if (!switched) 
                    a_next_state = a_ready;
                else if (setup_ready_read)
                    a_next_state = a_ready;
            end
            a_wait: begin
                if (cache_ready)
                    a_next_state = a_ready;
            end
        endcase
    end

    always_ff @(posedge clk) begin
        if (rst) 
            a_state <= a_ready;
        else 
            a_state <= a_next_state;
    end

endmodule