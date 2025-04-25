module dcache
import cache_types::*;
#(
  parameter integer ID              = 0,
  parameter integer WAYS            = 4,
  parameter integer SETS            = 16,
  parameter integer SET_BITS        = $clog2(SETS),
  parameter integer CACHELINE_BYTES = 32,
  parameter integer CACHELINE_BITS  = $clog2(CACHELINE_BYTES),
  parameter integer TAG_BITS        = 32 - SET_BITS - CACHELINE_BITS
) (
  input   logic           clk,
  input   logic           rst,

  // CPU Side Signals
  input  logic [31:0]     ufp_addr,
  input  logic [3:0]      ufp_rmask,
  input  logic [3:0]      ufp_wmask,
  output logic [31:0]     ufp_rdata,
  input  logic [31:0]     ufp_wdata,
  output logic            ufp_resp,

  // Coherence Side Signals
  input  req_msg_t        req_bus_msg,  // Active Request Bus Message
  output req_msg_t        req_bus_tx,   // Arbiter Message
  input  logic            req_bus_gnt,  // Arbiter Grant
  output logic            req_bus_req,  // Arbiter Request
  output logic            req_bus_busy, // Arbiter Stall

  input  resp_msg_t       resp_bus_msg, // Active Response Bus Message
  output resp_msg_t       resp_bus_tx,  // Arbiter Message
  input  logic            resp_bus_gnt, // Arbiter Grant
  output logic            resp_bus_req, // Arbiter Request
  output logic            resp_bus_busy, // Arbiter Stall

  // Inclusive Policy Signals
  input  logic            invalidate,
  input  logic [XLEN-1:0] invalidate_addr
);

  // Cache Control Signals
  logic [31:0]     dfp_addr;
  logic            dfp_read;
  logic            dfp_write;
  logic [255:0]    dfp_rdata;
  logic [255:0]    dfp_wdata;
  logic            dfp_resp;

  logic            cache_read_request;
  logic            cache_write_request;
  logic            write_from_cpu;
  logic            write_from_mem;

  logic            idle;
  logic            dirty;

  logic            cache_hit;
  logic [WAYS-1:0] cache_hit_vector;
  logic [WAYS-1:0] bus_hit_vector;

  logic            bus_request;

  logic            evict_update;
  logic [WAYS-1:0] evict_candidate;

  // Cache Arrays
  logic              tag_array_csb0    [WAYS];
  logic              tag_array_csb1    [WAYS];
  logic [TAG_BITS:0] tag_array_dout0   [WAYS];
  logic [TAG_BITS:0] tag_array_dout1   [WAYS];
  logic              tag_array_web0    [WAYS];

  logic              data_array_csb0   [WAYS];
  logic              data_array_csb1   [WAYS];
  logic [255:0]      data_array_dout0  [WAYS];
  logic [255:0]      data_array_dout1  [WAYS];
  logic [255:0]      data_array_din0   [WAYS];
  logic              data_array_web0   [WAYS];
  logic [31:0]       data_array_wmask  [WAYS];

  logic              dirty_array_din0  [WAYS];

  logic              valid_array_csb0  [WAYS];
  logic              valid_array_csb1  [WAYS];
  logic              valid_array_din0  [WAYS];
  logic              valid_array_dout0 [WAYS];
  logic              valid_array_dout1 [WAYS];
  logic              valid_array_web0  [WAYS];

  // UFP Address partition and register
  logic [31:0]               ufp_addr_reg;
  logic [3:0]                ufp_rmask_reg;
  logic [3:0]                ufp_wmask_reg;
  logic [31:0]               ufp_wdata_reg;
  logic [CACHELINE_BITS-1:0] block_offset;
  logic [TAG_BITS-1:0]       tag_val;
  logic [SET_BITS-1:0]       set_addr;
  logic [TAG_BITS-1:0]       bus_tag_val;
  logic [SET_BITS-1:0]       bus_set_addr;
  logic [255:0]              bus_rdata;

  assign block_offset = ufp_addr_reg[CACHELINE_BITS-1:0];

  assign tag_val      = ufp_addr_reg[31:SET_BITS+CACHELINE_BITS];
  assign set_addr     = idle ? ufp_addr[SET_BITS+CACHELINE_BITS-1:CACHELINE_BITS]
                             : ufp_addr_reg[SET_BITS+CACHELINE_BITS-1:CACHELINE_BITS];

  assign bus_tag_val  = req_bus_msg.addr[31:SET_BITS+CACHELINE_BITS];
  assign bus_set_addr = req_bus_msg.addr[SET_BITS+CACHELINE_BITS-1:CACHELINE_BITS];

  // Register signals because we're not pipelined yet
  always_ff @ (posedge clk) begin
    if (rst) begin
      ufp_addr_reg  <= '0;
      ufp_wmask_reg <= '0;
      ufp_rmask_reg <= '0;
      ufp_wdata_reg <= '0;
    end
    else if (idle) begin
      ufp_addr_reg  <= ufp_addr;
      ufp_wmask_reg <= ufp_wmask;
      ufp_rmask_reg <= ufp_rmask;
      ufp_wdata_reg <= ufp_wdata;
    end
  end

  always_comb begin
    // DRAM signals
    dfp_wdata = 'x;
    for (int i = 0; i < WAYS; i++) begin
      if (evict_candidate[i]) begin
        dfp_wdata = data_array_dout0[i];
      end
    end

    // By default use address from CPU
    dfp_addr = {ufp_addr_reg[31:CACHELINE_BITS], 5'b0};

    // Cache Request Logic
    if (idle) begin
      cache_read_request  = |ufp_rmask;
      cache_write_request = |ufp_wmask;
    end
    else begin
      cache_read_request  = |ufp_rmask_reg;
      cache_write_request = |ufp_wmask_reg;
    end

    // Writeback logic
    dirty = 1'b0;

    // Calculate hit vector and data output
    ufp_rdata = 32'b0;
    for (int i = 0; i < WAYS; i++) begin
      // Don't write unless memory or cpu writing
      tag_array_web0[i]     = 1'b1;
      data_array_web0[i]    = 1'b1;
      data_array_wmask[i]   = 32'b0;
      data_array_din0[i]    = 256'b0;
      valid_array_din0[i]   = 1'b0;
      valid_array_web0[i]   = 1'b1;
      dirty_array_din0[i]   = 1'b0;

      // Checks cache tag hits
      cache_hit_vector[i] = 1'b0;
      if (tag_array_dout0[i][TAG_BITS-1:0] == tag_val) begin
        // Mark as hit and set the cpu rdata correctly
        cache_hit_vector[i] = valid_array_dout0[i];
        ufp_rdata = data_array_dout0[i][({block_offset, 3'b0})+:32];

        // Write to cache if doing a store and there is a hit
        if (write_from_cpu) begin
          tag_array_web0[i]   = 1'b0;
          data_array_web0[i]  = 1'b0;
          data_array_din0[i]  = 256'b0 | (ufp_wdata_reg << ({block_offset, 3'b0}));
          data_array_wmask[i] = 32'b0 | ufp_wmask_reg << (block_offset);

          // Mark array as valid and dirty during a write from cpu
          valid_array_din0[i] = 1'b1;
          valid_array_web0[i] = 1'b0;
          dirty_array_din0[i] = 1'b1;
        end
      end

      // Checks bus tag hits
      bus_rdata = 'x;
      bus_hit_vector[i] = 1'b0;
      if (tag_array_dout1[i][TAG_BITS-1:0] == bus_tag_val) begin
        bus_rdata = data_array_dout1[i];
        bus_hit_vector[i] = valid_array_dout1[i];
      end

      bus_request = req_bus_msg.valid;

      // Write to cache after writeback completes
      // Only overwrite the eviction candidate
      if (write_from_mem && evict_candidate[i]) begin
        cache_hit_vector[i] = 1'b1;
        tag_array_web0[i]  = 1'b0;
        data_array_web0[i] = 1'b0;
        data_array_wmask[i] = ~32'b0;
        data_array_din0[i] = dfp_rdata;

        // Mark data from memory as clean and valid
        valid_array_din0[i] = 1'b1;
        valid_array_web0[i] = 1'b0;
        dirty_array_din0[i] = 1'b0;
      end

      // Dirty bit write back logic
      // Set the dfp_addr correctly for writeback
      if (evict_candidate[i] && valid_array_dout0[i] && tag_array_dout0[i][TAG_BITS]) begin
        dirty = 1'b1;
        if (dfp_write) begin
          dfp_addr = {tag_array_dout0[i][TAG_BITS-1:0], set_addr, 5'b0};
        end
      end
    end

    // Cache Hit/WB and Data Logic and
    cache_hit = |cache_hit_vector;

    // Update eviction logic when cache is replying
    evict_update = ~ufp_resp;
  end

  generate for (genvar i = 0; i < WAYS; i++) begin : gen_sram_arrays
    dcache_data_array data_array (
      .clk0       (clk),
      .csb0       (data_array_csb0[i]),
      .web0       (data_array_web0[i]),
      .wmask0     (data_array_wmask[i]),
      .addr0      (set_addr),
      .din0       (data_array_din0[i]),
      .dout0      (data_array_dout0[i]),
      .clk1       (clk),
      .csb1       (data_array_csb1[i]),
      .addr1      (bus_set_addr),
      .dout1      (data_array_dout1[i])
    );
    dcache_tag_array tag_array (
      .clk0       (clk),
      .csb0       (tag_array_csb0[i]),
      .web0       (tag_array_web0[i]),
      .addr0      (set_addr),
      .din0       ({dirty_array_din0[i], tag_val}),
      .dout0      (tag_array_dout0[i]),
      .clk1       (clk),
      .csb1       (tag_array_csb1[i]),
      .addr1      (bus_set_addr),
      .dout1      (tag_array_dout1[i])
    );
    ff_array_rwr #(.WIDTH(1)) valid_array (
      .clk0       (clk),
      .rst0       (rst),
      .csb0       (valid_array_csb0[i]),
      .web0       (valid_array_web0[i]),
      .addr0      (set_addr),
      .din0       (valid_array_din0[i]),
      .dout0      (valid_array_dout0[i]),
      .clk1       (clk),
      .rst1       (rst),
      .csb1       (valid_array_csb1[i]),
      .addr1      (bus_set_addr),
      .dout1      (valid_array_dout1[i])
    );
  end endgenerate

  dcache_coherence #(
    .ID(ID),
    .WAYS(WAYS),
    .SETS(SETS)
  ) dcache_coherence0 (
    .clk(clk),
    .rst(rst),
    .dfp_addr(dfp_addr),
    .dfp_read(dfp_read),
    .dfp_write(dfp_write),
    .dfp_wdata(dfp_wdata),
    .dfp_rdata(dfp_rdata),
    .dfp_resp(dfp_resp),
    .bus_rdata(bus_rdata),
    .cache_read_request(cache_read_request),
    .cache_write_request(cache_write_request),
    .cache_hit_vector(cache_hit_vector),
    .bus_hit_vector(bus_hit_vector),
    .evict_candidate(evict_candidate),
    .req_bus_msg(req_bus_msg),
    .req_bus_tx(req_bus_tx),
    .req_bus_gnt(req_bus_gnt),
    .req_bus_req(req_bus_req),
    .req_bus_busy(req_bus_busy),
    .resp_bus_msg(resp_bus_msg),
    .resp_bus_tx(resp_bus_tx),
    .resp_bus_gnt(resp_bus_gnt),
    .resp_bus_req(resp_bus_req),
    .resp_bus_busy(resp_bus_busy),
    .invalidate(invalidate),
    .invalidate_addr(invalidate_addr)
  );

  dcache_control #(
    .WAYS(WAYS)
  ) dcache_control0 (
    .clk(clk),
    .rst(rst),
    .cache_hit(cache_hit),
    .cache_read_request(cache_read_request),
    .cache_write_request(cache_write_request),
    .ufp_resp(ufp_resp),
    .dfp_resp(dfp_resp),
    .dfp_read(dfp_read),
    .dfp_write(dfp_write),
    .bus_request(bus_request),
    .tag_array_csb0(tag_array_csb0),
    .data_array_csb0(data_array_csb0),
    .valid_array_csb0(valid_array_csb0),
    .tag_array_csb1(tag_array_csb1),
    .data_array_csb1(data_array_csb1),
    .valid_array_csb1(valid_array_csb1),
    .write_from_mem(write_from_mem),
    .write_from_cpu(write_from_cpu),
    .idle(idle),
    .dirty(dirty)
  );

  plru #(
    .WAYS(WAYS),
    .SETS(SETS)
  ) plru0 (
    .clk(clk),
    .rst(rst),
    .evict_update(evict_update),
    .set_addr(set_addr),
    .cache_hit_vector(cache_hit_vector),
    .evict_candidate(evict_candidate)
  );

endmodule
