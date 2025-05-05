module mutative_control 
import mutative_types::*;
(
    input   logic           clk,
    input   logic           rst, 
    input logic real_cache_valid,
    input logic real_cache_hit,
    input logic full_assoc_hit,
    input logic real_cache_full,
    input logic full_assoc_full,
    input logic cache_ready,
    input logic cpu_req,
    input logic switch_dir,
    input logic switch_valid,

    output logic [1:0] setup,
    output logic setup_ready
);

    logic [31:0] hit_counter;
    logic [31:0] request_counter;
    logic [31:0] hit_counter_next;
    logic [31:0] request_counter_next;

    enum logic [2:0] {
        s_idle, s_update, s_waiting
    } control_state, control_state_next;

    logic [32:0] switch_counter;
    logic [32:0] switch_counter_next;
    logic [1:0] setup_next;
    always_ff @( posedge clk ) begin
        if (rst) begin
            control_state <= s_idle;
            setup <= 2'b00; //defaulting to DM
            switch_counter <= '0;
            hit_counter <= '0;
            request_counter <= '0;
        end else begin
            control_state <= control_state_next;
            setup <= setup_next;
            switch_counter <= switch_counter_next;
            hit_counter <= hit_counter_next;
            request_counter <= request_counter_next;
        end
    end

    always_comb begin
        control_state_next = control_state;
        setup_next = setup;
        switch_counter_next = switch_counter;
        hit_counter_next = hit_counter;
        request_counter_next = request_counter;
        
        setup_ready = 1'b0;

        unique case (control_state)
            s_idle: begin 
                // if(switch_counter >= 50) begin //random number
                //     switch_counter_next = '0;
                //     if(setup < 3)
                //         setup_next = setup+1;
                // end
                if (switch_valid) begin
                    if (switch_dir == 1'b1) begin
                        if (setup < 3)
                            setup_next = setup+1;
                    end
                    setup_ready = '1;
                end
                if(cpu_req) begin
                    control_state_next = s_update;
                end
            end
            s_update: begin
                request_counter_next++;
                if(real_cache_valid) begin //ignoring compulsory misses
                    if( (!real_cache_hit && full_assoc_hit) || (!real_cache_hit && !full_assoc_hit && !real_cache_full)) begin //conflict miss
                        switch_counter_next+=2;
                    end else if((!real_cache_hit && !full_assoc_hit && real_cache_full && full_assoc_full)) //capacity miss
                        switch_counter_next -= 1;
                        else begin
                        hit_counter_next++;
                    end
                end

                control_state_next = (cache_ready) ? s_idle : s_waiting;
            end
            s_waiting: begin
                if(cache_ready) begin
                    control_state_next = s_idle;
                end
            end
            default: begin

            end
        endcase
    end



endmodule