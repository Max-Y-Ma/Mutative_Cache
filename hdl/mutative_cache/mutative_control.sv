module mutative_control
import mutative_types::*;
# (
    parameter interger WAYS = 8
) (
    input logic                       clk,
    input logic                       rst,

    // Prediction Signals
    input  logic                      dfp_resp,
    output logic [SET_BITS-1:0]       flush_set_addr,
    output logic [255:0]              flush_dfp_wdata,
    output logic                      flush_dfp_write,
    output logic [31:0]               flush_dfp_addr,

    input  logic [WAYS-1:0]           dirty_vector,
    input  logic [CACHELINE_SIZE-1:0] dirty_data_vector [WAYS],

    output logic                      setup_ready,
    input  logic                      setup_valid,
    input  logic                      setup_update,
    output logic                      flush_stall,
    output logic [1:0]                setup
);

    // Setup Control Logic
    logic [1:0]                setup_reg;
    logic [1:0]                setup_next;

    logic                      setup_ready_next;

    logic                      flush_stall_reg;
    logic                      flush_stall_next;

    logic [WAYS-1:0]           flush_vector;
    logic [CACHELINE_SIZE-1:0] flush_data_vector [WAYS];

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

    // Flush State Machine Next State Logic
    typedef enum logic [1:0] {
        f_idle,  // Wait for a flush signal, read the first physical set
        f_check, // Check for dirty bits, set flush vector, read the next physical set
        f_flush, // Flush data according to flush vector, clear flush vector on iteration, move to check when flush vector is fully cleared and increment counter
        f_wait   // Wait for DFP response
    } mutative_cache_flush_t;

    // Dirty Bits Update Logic
    always_ff @(posedge clk) begin
        if (rst) begin
            flush_vector <= '0;
        end
        else begin
            if () begin
                flush_vector <= dirty_vector;
            end
            else if () begin
                flush_vector[i] <= '0;
            end
        end
    end

    // Set Address Update Logic
    always_ff @(posedge clk) begin
        if (rst) begin
            flush_set_addr <= '0;
        end else begin
            if () begin
                flush_set_addr <= flush_set_addr + 1;
            end
        end
    end

    always_comb begin
        setup_ready_next = '0;
        control_state_next = control_state;
        flush_stall_next = flush_stall_reg;

        unique case (control_state)
            f_idle : begin
                if (setup_valid) begin
                    control_state_next = f_check;
                    flush_stall_next   = '1;
                end
            end
            f_check : begin

            end
            f_flush : begin

            end
            f_wait : begin

            end
            default: begin
            end
        endcase
    end

    assign setup_ready = setup_ready_next;
    assign flush_stall = flush_stall_next;

    // Flush State Machine Sequential Logic
    always_ff @(posedge clk) begin
        if (rst) begin
            flush_stall_reg <= '0;
            control_state   <= s_idle;
        end else begin
            flush_stall_reg <= flush_stall_next;
            control_state   <= control_state_next;
        end
    end

endmodule
