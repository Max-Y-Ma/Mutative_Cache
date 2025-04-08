module icache
import cache_types::*;
#(
  localparam WORDSIZE             = 32,
  localparam HALF_WORDSIZE        = WORDSIZE / 2,
  localparam WORDSIZE_BYTES       = WORDSIZE / 8,
  parameter  SETS                 = 256,
  localparam SET_WIDTH            = $clog2(SETS),
  parameter  CACHELINE            = 64,
  localparam CACHELINE_BYTES      = CACHELINE / 8,
  localparam CACHELINE_WIDTH      = $clog2(CACHELINE_BYTES),
  localparam TAG_WIDTH            = WORDSIZE - SET_WIDTH - CACHELINE_WIDTH,
  localparam SRAM_DATA            = 1 + TAG_WIDTH + CACHELINE
) (
  input   logic           clk,
  input   logic           rst,

  // cpu side signals, ufp -> upward facing port
  input   logic   [31:0]  ufp_addr,
  input   logic   [3:0]   ufp_rmask,
  output  logic   [31:0]  ufp_rdata,
  output  logic           ufp_resp,

  // memory side signals, dfp -> downward facing port
  output  logic   [31:0] dfp_addr,
  output  logic          dfp_read,
  output  logic          dfp_write,
  input   logic   [63:0] dfp_rdata,
  output  logic   [63:0] dfp_wdata,
  input   logic          dfp_resp
);

  /* Cache Control Signals */
  logic cache_read_request;
  logic write_from_mem;
  logic ready;
  logic cache_hit;
  logic misaligned;
  logic save_sram_dout;
  logic save_dfp_rdata;
  logic second_done;

  /* Valid, tag, and cacheline control signals */
  /* Format: {valid(1) | tag(21) | data(64) } */
  logic                       sram_array_csb0;
  logic [SRAM_DATA-1:0]       sram_array_dout0;
  logic [SRAM_DATA-1:0]       sram_array_din0;
  logic                       sram_array_web0;

  /* UFP Address partition and register */
  logic [WORDSIZE-1:0]        ufp_addr_reg;
  logic [WORDSIZE_BYTES-1:0]  ufp_rmask_reg;
  
  logic [TAG_WIDTH-1:0]       tag;
  logic [SET_WIDTH-1:0]       set_addr;
  logic [CACHELINE_WIDTH-1:0] block_offset;

  assign tag          = ufp_addr_reg[WORDSIZE-1:SET_WIDTH+CACHELINE_WIDTH];
  assign block_offset = ufp_addr_reg[CACHELINE_WIDTH-1:0];

  /* Buffer read request address and mask for pipelined icache */
  always_ff @(posedge clk, posedge rst) begin
    if (rst) begin
      ufp_addr_reg  <= '0;
      ufp_rmask_reg <= '0;
    end
    else if (ready || second_done) begin
      ufp_addr_reg  <= ufp_addr;
      ufp_rmask_reg <= ufp_rmask;
    end
    else if (save_sram_dout || save_dfp_rdata) begin
      ufp_addr_reg  <= ufp_addr_reg + 2;
      ufp_rmask_reg <= ufp_rmask_reg;
    end
  end

  /* Upper 16-bit buffer for cacheline */
  logic [HALF_WORDSIZE-1:0] upper_half;
  always_ff @(posedge clk, posedge rst) begin
    if (rst) begin
      upper_half <= '0;
    end
    else if (save_sram_dout) begin
      upper_half <= sram_array_dout0[CACHELINE-1 -: HALF_WORDSIZE];
    end
    else if (save_dfp_rdata) begin
      upper_half <= dfp_rdata[CACHELINE-1 -: HALF_WORDSIZE];
    end
  end

  always_comb begin
    // Check if address crosses cacheline
    misaligned = (ufp_addr_reg[CACHELINE_WIDTH-1:0] == unsigned'(CACHELINE_BYTES - 2));

    // Set downward facing port address and write data
    dfp_addr  = ufp_addr_reg[WORDSIZE-1:CACHELINE_WIDTH] << CACHELINE_WIDTH;
    dfp_wdata = sram_array_dout0[CACHELINE-1:0];

    // Cache Request Register Logic
    if (ready || second_done) begin
      cache_read_request  = |ufp_rmask;
      set_addr            = ufp_addr[SET_WIDTH+CACHELINE_WIDTH-1:CACHELINE_WIDTH];
    end
    else if (save_sram_dout) begin
      // Read second cacheline address for misalignment
      cache_read_request  = |ufp_rmask_reg;
      set_addr            = ufp_addr_reg[SET_WIDTH+CACHELINE_WIDTH-1:CACHELINE_WIDTH] + 1'b1;
    end
    else if(save_dfp_rdata) begin
      // Read second cacheline address for misalignment
      cache_read_request  = |ufp_rmask_reg;
      set_addr            = ufp_addr_reg[SET_WIDTH+CACHELINE_WIDTH-1:CACHELINE_WIDTH];
    end
    else begin
      cache_read_request  = |ufp_rmask_reg;
      set_addr            = ufp_addr_reg[SET_WIDTH+CACHELINE_WIDTH-1:CACHELINE_WIDTH];
    end

    // Calculate tag hits and set upward facing port data output
    cache_hit = '0;
    ufp_rdata = '0;
    if (sram_array_dout0[TAG_WIDTH+CACHELINE-1:CACHELINE] == tag) begin
      // Mark as hit if cacheline is valid
      cache_hit = sram_array_dout0[SRAM_DATA-1];

      // Return matching upward facing data
      if (second_done) begin
        ufp_rdata = {sram_array_dout0[{block_offset, 3'b000} +: HALF_WORDSIZE], upper_half};
      end
      else begin
        ufp_rdata = sram_array_dout0[{block_offset, 3'b000} +: WORDSIZE];
      end
    end

    // Update from memory fetch
    sram_array_din0  = '0;
    sram_array_web0  = '1;
    // sram_array_wmask = '0;
    if (write_from_mem) begin
      // Write to cache after writeback completes
      sram_array_web0  = '0;

      // Construct full cache line with valid bit, tag, and data
      // Format: {valid(1) | tag(21) | data(64) }
      sram_array_din0 = {1'b1, tag, dfp_rdata[CACHELINE-1:0]};
    end
  end

  logic dummy_bit; // Last minute change, move valid to ff array bmn4 11/7/2024

  ff_array #(
    .S_INDEX(SET_WIDTH),
    .WIDTH(1)
  ) icache_ff0 (
    .clk0(clk),
    .rst0(rst),

    .csb0(sram_array_csb0),
    .web0(sram_array_web0),
    .addr0(set_addr),
    .din0(sram_array_din0[SRAM_DATA-1]),
    .dout0(sram_array_dout0[SRAM_DATA-1])
  );

  /* ARM SRAM IP */
  icache_sram icache_sram0 (
    .CLK(clk),
    .CEN(sram_array_csb0),
    .WEN(sram_array_web0),
    .A(set_addr),
    .D(sram_array_din0),
    .Q({dummy_bit, sram_array_dout0[SRAM_DATA-2:0]}),
    .EMA(3'b000),
    .RETN(1'b1)
  );

  icache_control cache_control0 (
    .clk(clk),
    .rst(rst),
    .cache_hit(cache_hit),
    .misaligned(misaligned),
    .cache_read_request(cache_read_request),
    .ufp_resp(ufp_resp),
    .dfp_resp(dfp_resp),
    .dfp_read(dfp_read),
    .dfp_write(dfp_write),
    .sram_array_csb0(sram_array_csb0),
    .write_from_mem(write_from_mem),
    .ready(ready),
    .save_sram_dout(save_sram_dout),
    .save_dfp_rdata(save_dfp_rdata),
    .second_done(second_done)
  );

endmodule
