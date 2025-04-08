module icache_control
import cache_types::*;
(
  input logic  clk, rst,

  // Cache Datapath Interface
  input logic  cache_hit,
  input logic  misaligned,
  input logic  cache_read_request,

  // UFP Interface
  output logic ufp_resp,

  // DFP Interface
  input  logic dfp_resp,
  output logic dfp_read,
  output logic dfp_write,

  // Chip Select Signals
  output logic sram_array_csb0,

  // SRAM Controls
  output logic write_from_mem,

  // Cache Control Signals
  output logic ready,
  output logic save_sram_dout,
  output logic save_dfp_rdata,
  output logic second_done
);

icontroller_state_t curr_state;
icontroller_state_t next_state;

always_comb begin
  // Defaults
  next_state     = curr_state;
  write_from_mem = 1'b0;
  dfp_write      = 1'b0;
  dfp_read       = 1'b0;
  ufp_resp       = 1'b0;
  ready          = 1'b0;
  save_sram_dout = 1'b0;
  save_dfp_rdata = 1'b0;
  second_done    = 1'b0;

  // Default Chip Select Signals
  sram_array_csb0 = 1'b1;

  unique case (curr_state)
    IDLE: begin
      ready = 1'b1;
      if (cache_read_request) begin
        /* Assert chip select signals */
        sram_array_csb0 = 1'b0;

        next_state = CHECK;
      end
    end
    CHECK: begin
      if (cache_hit) begin
        if (misaligned) begin
          /* Read request is misaligned and hit, save the first cacheline
          and fetch the second cacheline */
          save_sram_dout = 1'b1;

          /* Assert chip select signals */
          sram_array_csb0 = 1'b0;

          next_state = CHECK_SECOND;
        end
        else begin
          /* Read request is aligned and hit, respond to next request */
          ready    = 1'b1;
          ufp_resp = 1'b1;
          if (cache_read_request) begin
            /* Assert chip select signals */
            sram_array_csb0 = 1'b0;

            next_state = CHECK;
          end
          else begin
            next_state = IDLE;
          end
        end
      end
      else begin
        /* If read is misaligned and missed, fetch first cacheline */
        next_state = misaligned ? FETCH_FIRST : FETCH;
      end
    end
    FETCH: begin
      dfp_read = 1'b1;
      if (dfp_resp) begin
        /* Assert chip select signals */
        sram_array_csb0 = 1'b0;

        write_from_mem = 1'b1;
        next_state = FETCH_WAIT;
      end
      else begin
        next_state = FETCH;
      end
    end
    FETCH_WAIT: begin
      /* Assert chip select signals */
      sram_array_csb0 = 1'b0;
      
      next_state = CHECK;
    end
    CHECK_SECOND: begin
      if (cache_hit) begin
        /* Assert second fetch complete */
        second_done = 1'b1;
        ufp_resp    = 1'b1;
        if (cache_read_request) begin
          /* Assert chip select signals */
          sram_array_csb0 = 1'b0;

          next_state = CHECK;
        end
        else begin
          next_state = IDLE;
        end
      end
      else begin
        next_state = FETCH_SECOND;
      end
    end
    FETCH_FIRST: begin
      dfp_read = 1'b1;
      if (dfp_resp) begin
        /* Assert chip select signals */
        sram_array_csb0 = 1'b0;

        save_dfp_rdata = 1'b1;
        write_from_mem = 1'b1;
        next_state = CHECK_SECOND;
      end
      else begin
        next_state = FETCH_FIRST;
      end
    end
    FETCH_SECOND: begin
      dfp_read = 1'b1;
      if (dfp_resp) begin
        /* Assert chip select signals */
        sram_array_csb0 = 1'b0;

        write_from_mem = 1'b1;
        next_state = WAIT_SECOND;
      end
      else begin
        next_state = FETCH_SECOND;
      end
    end
    WAIT_SECOND: begin
      /* Assert chip select signals */
      sram_array_csb0 = 1'b0;

      next_state = CHECK_SECOND;
    end
  endcase
end

// Next state flop
always_ff @ (posedge clk, posedge rst) begin
  if (rst) curr_state <= IDLE;
  else     curr_state <= next_state;
end

endmodule
