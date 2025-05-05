module associativity
import mutative_types::*;
(
    input  logic            clk,
    input  logic            rst,
    input  logic            cache_wen,
    input  logic            dirty_en,
    input  logic [31:0]     ufp_addr_ff,
    input  logic [WAYS-1:0] way_we,
    input  cache_address_t  cache_address,
    input  logic            cache_ready,
    input  logic            real_cache_hit,

    // Upscale and Downscale Logic
    input  logic [1:0]      setup,
    input  logic            cpu_request,
    input  logic            setup_ready,
    output logic            setup_valid,
    output logic            setup_update
);

    logic [FULL_TAG_BITS-1:0]   full_assoc_tag;
    full_assoc_t                full_assoc_cache[SET_SIZE*WAYS];
    logic [FULL_ASSOC_BITS-1:0] full_assoc_hit_idx;

    logic                       real_cache_full;
    logic                       full_assoc_full;
    logic                       full_assoc_hit;

    assign full_assoc_tag = ufp_addr_ff >> OFFSET_BITS;
    assign valid_bit = full_assoc_cache[full_assoc_hit_idx].valid;

    always_comb begin
        full_assoc_hit = 1'b0;
        full_assoc_hit_idx = '0;
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

    // Prediction Logic
    typedef enum logic [2:0] {
        s_idle, s_update, s_waiting
    } assoc_state_t;

    assoc_state_t control_state;
    assoc_state_t control_state_next;

    logic [31:0] hit_counter;
    logic [31:0] hit_counter_next;
    logic [31:0] request_counter;
    logic [31:0] request_counter_next;
    logic [32:0] switch_counter;
    logic [32:0] switch_counter_next;

    logic        setup_valid_reg;
    logic        setup_valid_next;
    logic        setup_update_reg;
    logic        setup_update_next;

    always_ff @( posedge clk ) begin
        if (rst) begin
            control_state   <= s_idle;
            switch_counter  <= '0;
            hit_counter     <= '0;
            request_counter <= '0;
        end else begin
            control_state   <= control_state_next;
            switch_counter  <= switch_counter_next;
            hit_counter     <= hit_counter_next;
            request_counter <= request_counter_next;
        end
    end

    // Upscale and Downscale Logic
    always_comb begin
        setup_valid_next  = setup_valid_reg;
        setup_update_next = setup_update_reg;

        if (control_state == s_idle) begin
          if(switch_counter >= 45) begin
              if(setup < 3) begin
                  setup_valid_next = '1;
                  setup_update_next = '0;
              end
          end
          else if (switch_counter <= 15) begin
              if (setup > 0) begin
                  setup_valid_next = '1;
                  setup_update_next = '1;
              end
          end
        end

        if (setup_ready) begin
            setup_valid_next = '0;
        end
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            setup_valid_reg  <= '0;
            setup_update_reg <= '0;
        end else begin
            setup_valid_reg  <= setup_valid_next;
            setup_update_reg <= setup_update_next;
        end
    end

    assign setup_valid  = setup_valid_next | setup_valid_reg;
    assign setup_update = setup_update_next;

    always_comb begin
        // Prediction Update Logic
        control_state_next   = control_state;
        switch_counter_next  = switch_counter;
        hit_counter_next     = hit_counter;
        request_counter_next = request_counter;

        unique case (control_state)
            s_idle: begin
                if(switch_counter >= 45) begin
                    switch_counter_next = 30;
                end
                else if (switch_counter <= 15) begin
                    switch_counter_next = 30;
                end

                if(cpu_request) begin
                    control_state_next = s_update;
                end
            end
            s_update: begin
                request_counter_next++;
                if(valid_bit) begin // Ignoring Compulsory Misses
                    if( (!real_cache_hit && full_assoc_hit) || (!real_cache_hit && !full_assoc_hit && !real_cache_full)) begin // Conflict Miss
                        switch_counter_next += 2;
                    end
                    else if((!real_cache_hit && !full_assoc_hit && real_cache_full && full_assoc_full)) begin // Capacity Miss
                        switch_counter_next -= 1;
                    end
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
