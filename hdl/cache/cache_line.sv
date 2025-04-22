module cache_line
import cache_types::*;
(
  input logic clk, rst,

  // Request Interface
  output logic [31:0]  bmem_addr,
  output logic         bmem_read,
  output logic         bmem_write,
  output logic [63:0]  bmem_wdata,

  // Queue interface
  input  logic         bmem_ready,

  // Response Interface
  input  logic [31:0]  bmem_raddr,
  input  logic [63:0]  bmem_rdata,
  input  logic         bmem_rvalid,

  // L2Cache Interface
  input  logic [31:0]  l2cache_addr,
  input  logic         l2cache_read,
  input  logic         l2cache_write,
  output logic [255:0] l2cache_rdata,
  input  logic [255:0] l2cache_wdata,
  output logic         l2cache_resp
);

// Stay in serialize / deserialize for three times
logic [1:0] serdes_count;
logic [1:0] next_serdes_count;

// Cache States
cacheline_state_t curr_state;
cacheline_state_t next_state;

// Cacheline Read Buffer
logic [255:0] line_buffer;
logic [255:0] next_line_buffer;

// Cache Logic
logic [31:0]  cache_addr;
logic         cache_read;
logic         cache_write;
logic [255:0] cache_rdata;
logic [255:0] cache_wdata;
logic         cache_resp;
logic         cache_req;

assign cache_addr  = l2cache_addr;
assign cache_read  = l2cache_read;
assign cache_write = l2cache_write;
assign cache_wdata = l2cache_wdata;

assign l2cache_rdata = cache_rdata;
assign l2cache_resp  = cache_resp;

// Next state FF
always_ff @ (posedge clk) begin
  if (rst) begin
    curr_state   <= LINE_IDLE;
    serdes_count <= '0;
  end
  else begin
    curr_state   <= next_state;
    serdes_count <= next_serdes_count;
    line_buffer  <= next_line_buffer;
  end
end

// Next state / output logic
always_comb begin
  // Default Values
  bmem_addr         = 'x;
  bmem_read         = '0;
  bmem_write        = '0;
  bmem_wdata        = 'x;
  next_state        = curr_state;
  next_serdes_count = serdes_count;
  next_line_buffer  = line_buffer;

  // Cache Request Logic
  cache_resp  = '0;
  cache_rdata = line_buffer;
  cache_req   = cache_read | cache_write;

  unique case (curr_state)
    LINE_IDLE: begin
      // Process request
      if (cache_req) begin
        bmem_addr = cache_addr;
        if (cache_write) begin
          bmem_write        = cache_write;
          bmem_wdata        = cache_wdata[63:0];
          next_serdes_count = 2'b01;
          next_state        = SERIALIZE;
        end
        else begin
          bmem_read  = cache_read;
          next_state = WAIT;
        end
      end
    end
    SERIALIZE: begin
      // Only do a new thing if bmem is ready
      bmem_write = 1'b1;
      bmem_wdata = cache_wdata[(serdes_count*64)+:64];
      bmem_addr  = cache_addr;

      if (bmem_ready) begin
        if (serdes_count == 2'b11) begin
          // Tell cache that memory is ready
          cache_resp = 1'b1;

          // Reset to IDLE
          next_serdes_count = '0;
          next_state        = LINE_IDLE;
        end
        else begin
          next_serdes_count = serdes_count + 1'b1;
        end
      end
    end
    WAIT: begin
      if (bmem_rvalid) begin
        // Service buffer
        next_line_buffer[63:0] = bmem_rdata;
        next_state             = DESERIALIZE;
        next_serdes_count      = 2'b01;
      end
    end
    DESERIALIZE: begin
      // Service buffer
      next_line_buffer[(serdes_count*64)+:64] = bmem_rdata;

      if (serdes_count == 2'b11) begin
        // To DONE State
        next_serdes_count = '0;
        next_state        = DESERIALIZE_DONE;
      end
      else begin
        next_serdes_count = serdes_count + 1'b1;
      end
    end
    DESERIALIZE_DONE: begin
      // Tell cache that memory is ready
      cache_resp = 1'b1;
      next_state = LINE_IDLE;
    end
    default: begin end
  endcase
end

endmodule
