module mutative_control
import mutative_types::*;
(
    input logic                       clk,
    input logic                       rst,

    // Prediction Signals
    input  logic                      dfp_resp,
    output logic [SET_BITS-1:0]       flush_set_addr,
    output logic [255:0]              flush_dfp_wdata,
    output logic                      flush_dfp_write,
    output logic [31:0]               flush_dfp_addr,

    input  logic [WAYS-1:0]           valid_vector,
    input  logic [WAYS-1:0]           dirty_vector,
    input  logic [TAG_BITS-1:0]       dirty_tag_vector  [WAYS],
    input  logic [CACHELINE_SIZE-1:0] dirty_data_vector [WAYS],

    output logic                      flush_tag_array_csb0   [WAYS-1:0],
    output logic                      flush_data_array_csb0  [WAYS-1:0],
    output logic                      flush_valid_array_csb0 [WAYS-1:0],

    output logic                      setup_ready,
    input  logic                      setup_valid,
    input  logic                      setup_update,
    output logic                      flush_stall,
    output logic [1:0]                setup
);

    // Flush State Machine Next State Logic
    typedef enum logic [1:0] {
        f_idle,  // Wait for a flush signal, read the first physical set
        f_check, // Check for dirty bits, set flush vector
        f_flush, // Flush data according to flush vector, clear flush vector on iteration,
                 // Move to f_check when flush vector is fully cleared and read the next physical set
        f_wait   // Wait for DFP response before returning to f_flush
    } mutative_cache_flush_t;

    mutative_cache_flush_t control_state;
    mutative_cache_flush_t control_state_next;

    // Setup Control Logic
    logic [1:0]                setup_reg;
    logic [1:0]                setup_next;

    logic                      setup_ready_reg;
    logic                      setup_ready_next;

    logic                      flush_stall_reg;
    logic                      flush_stall_next;

    logic                      flush_true;

    logic [WAYS-1:0]           flush_vector;
    logic [WAYS-1:0]           flush_valid_vector;
    logic [WAYS-1:0]           valid_vector_reg;
    logic [WAYS-1:0]           flush_vector_reg;
    logic [TAG_BITS-1:0]       flush_tag_vector  [WAYS];
    logic [CACHELINE_SIZE-1:0] flush_data_vector [WAYS];
    logic [SET_BITS-1:0]       flush_set_addr_reg;

    logic                      flush_check;
    logic                      flush_clean;
    logic [$clog2(WAYS)-1:0]   flush_clean_idx;
    logic                      flush_set_addr_inc;

    always_comb begin
        setup_next = setup_reg;

        if (setup_valid & setup_ready) begin
            if (setup_update) begin
                setup_next += (setup_next < 3);
            end
            else begin
                setup_next -= (setup_next > 0);
            end
        end
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            setup_reg <= '0;
        end
        else begin
            setup_reg <= setup_next;
        end
    end

    assign setup = setup_next;

    // Dirty Bits Update Logic
    always_ff @(posedge clk) begin
        if (rst) begin
            flush_vector_reg  <= '0;
            valid_vector_reg  <= '0;
            flush_tag_vector  <= '{default: '0};
            flush_data_vector <= '{default: '0};
        end
        else begin
            if (flush_check) begin
                flush_vector_reg  <= dirty_vector;
                valid_vector_reg  <= valid_vector;
                flush_tag_vector  <= dirty_tag_vector;
                flush_data_vector <= dirty_data_vector;
            end
            else if (flush_clean) begin
                flush_vector_reg[flush_clean_idx] <= '0;
            end
        end
    end

    assign flush_vector       = flush_check ? dirty_vector : flush_vector_reg;
    assign flush_valid_vector = flush_check ? valid_vector : valid_vector_reg;

    always_comb begin
        flush_true = '0;
        flush_clean_idx = '0;

        for (int i = 0; i < WAYS; i++) begin
            if (flush_valid_vector[i] && flush_vector[i]) begin
                flush_true = '1;
                flush_clean_idx = i;
            end
        end
    end

    // Set Address Update Logic
    always_ff @(posedge clk) begin
        if (rst || setup_ready) begin
            flush_set_addr_reg <= '0;
        end else begin
            if (flush_set_addr_inc) begin
                flush_set_addr_reg <= flush_set_addr_reg + 1;
            end
        end
    end

    assign flush_set_addr = flush_set_addr_inc ? flush_set_addr_reg + 1 : flush_set_addr_reg;

    always_comb begin
        flush_check        = '0;
        flush_clean        = '0;
        flush_set_addr_inc = '0;

        flush_dfp_wdata = '0;
        flush_dfp_write = '0;
        flush_dfp_addr  = '0;

        control_state_next = control_state;
        flush_stall_next   = flush_stall_reg;
        setup_ready_next   = setup_ready_reg;

        // Default Chip Select Signals
        for (int i = 0; i < WAYS; i++) begin
            flush_tag_array_csb0[i]   = 1'b1;
            flush_data_array_csb0[i]  = 1'b1;
            flush_valid_array_csb0[i] = 1'b1;
        end

        unique case (control_state)
            f_idle : begin
                if (setup_valid) begin
                    if (~setup_update && ~setup_ready) begin
                        flush_stall_next = '1;

                        // Assert Data SRAM Read Signals
                        for (int i = 0; i < WAYS; i++) begin
                            flush_tag_array_csb0[i]   = 1'b0;
                            flush_data_array_csb0[i]  = 1'b0;
                            flush_valid_array_csb0[i] = 1'b0;
                        end

                        control_state_next = f_check;
                    end
                    else begin
                        setup_ready_next = ~setup_ready_reg;
                    end
                end
            end
            f_check : begin
                if (flush_set_addr_reg != (SET_SIZE - 1)) begin
                    flush_check = '1;
                end

                if (flush_true) begin
                    control_state_next = f_flush;
                end
                else begin
                    if (flush_set_addr == (SET_SIZE - 1)) begin
                        flush_stall_next = '0;
                        setup_ready_next = ~setup_ready_reg;
                        control_state_next = f_idle;
                    end
                    else begin
                        // Assert Data SRAM Read Signals
                        flush_set_addr_inc = '1;
                        for (int i = 0; i < WAYS; i++) begin
                            flush_tag_array_csb0[i]   = 1'b0;
                            flush_data_array_csb0[i]  = 1'b0;
                            flush_valid_array_csb0[i] = 1'b0;
                        end

                        control_state_next = f_check;
                    end
                end
            end
            f_flush : begin
                if (flush_true) begin
                    flush_dfp_wdata = flush_data_vector[flush_clean_idx];
                    flush_dfp_write = '1;
                    flush_dfp_addr  = {flush_tag_vector[flush_clean_idx], flush_set_addr , {OFFSET_BITS{1'b0}}};
                    control_state_next = f_wait;
                end else begin
                    // Assert Data SRAM Read Signals
                    if (flush_set_addr_reg != (SET_SIZE - 1)) begin
                        flush_set_addr_inc = '1;
                    end
                    for (int i = 0; i < WAYS; i++) begin
                        flush_tag_array_csb0[i]   = 1'b0;
                        flush_data_array_csb0[i]  = 1'b0;
                        flush_valid_array_csb0[i] = 1'b0;
                    end

                    control_state_next = f_check;
                end
            end
            f_wait : begin
                flush_dfp_wdata = flush_data_vector[flush_clean_idx];
                flush_dfp_write = '1;
                flush_dfp_addr  = {flush_tag_vector[flush_clean_idx], flush_set_addr , {OFFSET_BITS{1'b0}}};
                if (dfp_resp) begin
                    flush_clean        = '1;
                    control_state_next = f_flush;
                end
            end
            default: begin
            end
        endcase
    end

    assign setup_ready = setup_ready_reg;
    assign flush_stall = flush_stall_next;

    // Flush State Machine Sequential Logic
    always_ff @(posedge clk) begin
        if (rst) begin
            control_state <= f_idle;
        end else begin
            control_state <= control_state_next;
        end
    end

    // Control Signals Sequential Logic
    always_ff @(posedge clk) begin
        if (rst) begin
            flush_stall_reg <= '0;
            setup_ready_reg <= '0;
        end else begin
            flush_stall_reg <= flush_stall_next;
            setup_ready_reg <= setup_ready_next;
        end
    end

endmodule
