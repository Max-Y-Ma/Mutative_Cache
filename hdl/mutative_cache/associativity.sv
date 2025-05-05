module associativity
import mutative_types::*;
(
    input  logic                         clk,
    input  logic                         rst,
    input  cache_address_t               cache_address,
    input  logic                         cpu_request,
    input  logic                         cache_ready,
    input  logic                         setup_ready,
    input  logic [1:0]                   setup,
    input  logic                         plru_bit0,

    output logic                         setup_update,
    output logic                         setup_valid
);

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

    logic [2:0] dm_way_index = cache_address.tag[2:0];
    logic [1:0] two_way_index = cache_address.tag[1:0];
    logic       four_way_index = cache_address.tag[0];

    logic       setup_ready_read;
    logic       switched;
    logic       true_set_index;

    logic       setup_valid_reg;
    logic       setup_valid_next;
    logic       setup_update_reg;
    logic       setup_update_next;

    typedef enum logic [2:0] {
      a_ready, a_wait, a_switch, a_switch_decision, a_switch_wait
    } assoc_state_t;

    assoc_state_t a_state;
    assoc_state_t a_next_state;

    always_ff @(posedge clk) begin
        switched <= setup_valid_next;
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
        setup_valid_next = setup_valid_reg;
        setup_update_next = setup_update_reg;

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
                    if (cpu_request) begin
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
                    setup_valid_next = '0;
                    case (setup)
                        2'b00: begin
                            if (total_dead_sets >= 82) begin
                                setup_update_next = '1;
                                setup_valid_next = '1;
                            end
                        end 
                        2'b01: begin
                            if (total_dead_sets >= 43 && total_saturated_sets <= 22) begin
                                setup_update_next = '1;
                                setup_valid_next = '1;
                            end else if (total_saturated_sets >= 43 && total_dead_sets <= 22) begin
                                setup_update_next = '0;
                                setup_valid_next = '1;
                            end
                        end 
                        2'b10: begin
                            if (total_dead_sets >= 21 && total_saturated_sets <= 11) begin
                                setup_update_next = '1;
                                setup_valid_next = '1;
                            end else if (total_saturated_sets >= 22 && total_dead_sets <= 11) begin
                                setup_update_next = '0;
                                setup_valid_next = '1;
                            end
                        end
                        2'b11: begin
                            if (total_dead_sets >= 11 && total_saturated_sets <= 5) begin
                                setup_update_next = '1;
                                setup_valid_next = '1;
                            end else if (total_saturated_sets >= 11 && total_dead_sets <= 5) begin
                                setup_update_next = '0;
                                setup_valid_next = '1;
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
                        setup_valid_next = '0;
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

    assign setup_valid  = setup_valid_next;
    assign setup_update = setup_update_next;

    always_ff @(posedge clk) begin
        if (rst) begin
            setup_valid_reg  <= '0;
            setup_update_reg <= '0;
        end else begin
            setup_valid_reg  <= setup_valid_next;
            setup_update_reg <= setup_update_next;
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
                else if (cpu_request)
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

    // Prediction Logic
    // typedef enum logic [2:0] {
    //     s_idle, s_update, s_waiting
    // } assoc_state_t;

    // assoc_state_t control_state;
    // assoc_state_t control_state_next;

    // logic [31:0] hit_counter;
    // logic [31:0] hit_counter_next;
    // logic [31:0] request_counter;
    // logic [31:0] request_counter_next;
    // logic [32:0] switch_counter;
    // logic [32:0] switch_counter_next;

    // always_ff @( posedge clk ) begin
    //     if (rst) begin
    //         control_state   <= s_idle;
    //         switch_counter  <= '0;
    //         hit_counter     <= '0;
    //         request_counter <= '0;
    //     end else begin
    //         control_state   <= control_state_next;
    //         switch_counter  <= switch_counter_next;
    //         hit_counter     <= hit_counter_next;
    //         request_counter <= request_counter_next;
    //     end
    // end

    // Upscale and Downscale Logic
    // always_comb begin
    //     setup_valid_next  = setup_valid_reg;
    //     setup_update_next = setup_update_reg;

    //     if (control_state == s_idle) begin
    //       if(switch_counter >= 45) begin
    //           if(setup < 3) begin
    //               setup_valid_next = '1;
    //               setup_update_next = '0;
    //           end
    //       end
    //       else if (switch_counter <= 15) begin
    //           if (setup > 0) begin
    //               setup_valid_next = '1;
    //               setup_update_next = '1;
    //           end
    //       end
    //     end

    //     if (setup_ready) begin
    //         setup_valid_next = '0;
    //     end
    // end

    // always_ff @(posedge clk) begin
    //     if (rst) begin
    //         setup_valid_reg  <= '0;
    //         setup_update_reg <= '0;
    //     end else begin
    //         setup_valid_reg  <= setup_valid_next;
    //         setup_update_reg <= setup_update_next;
    //     end
    // end

    // assign setup_valid  = setup_valid_next | setup_valid_reg;
    // assign setup_update = setup_update_next;

    // always_comb begin
    //     // Prediction Update Logic
    //     control_state_next   = control_state;
    //     switch_counter_next  = switch_counter;
    //     hit_counter_next     = hit_counter;
    //     request_counter_next = request_counter;

    //     unique case (control_state)
    //         s_idle: begin
    //             if(switch_counter >= 45) begin
    //                 switch_counter_next = 30;
    //             end
    //             else if (switch_counter <= 15) begin
    //                 switch_counter_next = 30;
    //             end

    //             if(cpu_request) begin
    //                 control_state_next = s_update;
    //             end
    //         end
    //         s_update: begin
    //             request_counter_next++;
    //             if(valid_bit) begin // Ignoring Compulsory Misses
    //                 if( (!real_cache_hit && full_assoc_hit) || (!real_cache_hit && !full_assoc_hit && !real_cache_full)) begin // Conflict Miss
    //                     switch_counter_next += 2;
    //                 end
    //                 else if((!real_cache_hit && !full_assoc_hit && real_cache_full && full_assoc_full)) begin // Capacity Miss
    //                     switch_counter_next -= 1;
    //                 end
    //                 else begin
    //                     hit_counter_next++;
    //                 end
    //             end

    //             control_state_next = (cache_ready) ? s_idle : s_waiting;
    //         end
    //         s_waiting: begin
    //             if(cache_ready) begin
    //                 control_state_next = s_idle;
    //             end
    //         end
    //         default: begin
    //         end
    //     endcase
    // end

endmodule
