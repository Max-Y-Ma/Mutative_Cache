module l2cache
import cache_types::*;
#(
  parameter  integer ID              = 0,
  parameter  integer WAYS            = 4,
  parameter  integer SETS            = 16,
  localparam integer SET_BITS        = $clog2(SETS),
  parameter  integer CACHELINE_BYTES = 32,
  localparam integer CACHELINE_BITS  = $clog2(CACHELINE_BYTES),
  localparam integer TAG_BITS        = 32 - SET_BITS - CACHELINE_BITS
) (
  input   logic           clk,
  input   logic           rst,

  // Coherence Side Signals
  input  req_msg_t        req_bus_msg,  // Active Request Bus Message
  output logic            req_bus_busy, // Arbiter Stall

  // Snoop Bus
  input  resp_msg_t       resp_bus_msg, // Active Response Bus Message
  output resp_msg_t       resp_bus_tx,  // Arbiter Message
  input  logic            resp_bus_gnt, // Arbiter Grant
  output logic            resp_bus_req, // Arbiter Request
  output logic            resp_bus_busy, // Arbiter Stall

  // Inclusive Policy Signals
  output logic            invalidate_req,
  input  logic            invalidate_resp,
  output logic [XLEN-1:0] invalidate_addr,
  input  logic [255:0]    invalidate_wdata,

  // Memory Side Signals
  output logic [31:0]     dfp_addr,
  output logic            dfp_read,
  output logic            dfp_write,
  input  logic [255:0]    dfp_rdata,
  output logic [255:0]    dfp_wdata,
  input  logic            dfp_resp
);

  // Cache Control Signals
  logic            ufp_resp;
  logic [255:0]    ufp_rdata;

  logic            cache_dfp_write;
  logic            resp_dfp_write;
  logic [255:0]    resp_dfp_wdata;

  logic            cache_read_request;
  logic            cache_write_request;
  logic            write_from_cpu;
  logic            write_from_mem;

  logic            idle;
  logic            dirty;

  logic            cache_hit;
  logic [WAYS-1:0] cache_hit_vector;
  logic [WAYS-1:0] resp_bus_hit_vector;

  logic            req_bus_request;
  logic            resp_bus_request;

  logic            evict_update;
  logic [WAYS-1:0] evict_candidate;

  logic            invalidate_done;

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
  req_msg_t                  req_bus_msg_reg;
  resp_msg_t                 resp_bus_msg_reg;
  logic [CACHELINE_BITS-1:0] req_bus_block_offset;
  logic [TAG_BITS-1:0]       req_bus_tag_val;
  logic [SET_BITS-1:0]       req_bus_set_addr;
  logic [TAG_BITS-1:0]       resp_bus_tag_val;
  logic [SET_BITS-1:0]       resp_bus_set_addr;
  logic [255:0]              resp_bus_rdata;

  assign req_bus_block_offset = req_bus_msg_reg.addr[CACHELINE_BITS-1:0];

  assign req_bus_tag_val      = req_bus_msg_reg.addr[31:SET_BITS+CACHELINE_BITS];
  assign req_bus_set_addr     = idle ? req_bus_msg.addr[SET_BITS+CACHELINE_BITS-1:CACHELINE_BITS]
                                     : req_bus_msg_reg.addr[SET_BITS+CACHELINE_BITS-1:CACHELINE_BITS];

  assign resp_bus_tag_val = resp_bus_msg[31:SET_BITS+CACHELINE_BITS];
  assign resp_bus_set_addr = resp_bus_msg[SET_BITS+CACHELINE_BITS-1:CACHELINE_BITS];

  assign req_bus_request = idle ? req_bus_msg.valid : req_bus_msg_reg.valid;
  assign resp_bus_request = resp_bus_msg.valid;

  // Stall Request Bus While Serving Current Request
  assign req_bus_busy = (cache_read_request | cache_write_request) & ~ufp_resp ;

  // Register signals because we're not pipelined yet
  always_ff @ (posedge clk) begin
    if (rst) begin
      req_bus_msg_reg <= '0;
      resp_bus_msg_reg <= '0;
    end
    else if (idle) begin
      req_bus_msg_reg <= req_bus_msg;
      resp_bus_msg_reg <= resp_bus_msg;
    end
  end

  always_comb begin
    // DRAM signals
    dfp_write = cache_dfp_write | resp_dfp_write | invalidate_resp;

    dfp_wdata = 'x;
    if (resp_bus_request && resp_dfp_write) begin
      dfp_wdata = resp_dfp_wdata;
    end
    else if (cache_dfp_write) begin
      for (int i = 0; i < WAYS; i++) begin
        if (evict_candidate[i]) begin
          dfp_wdata = data_array_dout0[i];
        end
      end
    end
    else if (invalidate_resp) begin
      dfp_wdata = invalidate_wdata;
    end

    // By default use address from Bus request
    dfp_addr = {req_bus_msg_reg.addr[31:CACHELINE_BITS], 5'b0};

    // Cache Request Logic
    if (idle) begin
      cache_read_request  = req_bus_request & (req_bus_msg.bus_tx == GETS | req_bus_msg.bus_tx == GETM);
      cache_write_request = req_bus_request & (req_bus_msg.bus_tx == PUTM);
    end
    else begin
      cache_read_request  = req_bus_request & (req_bus_msg_reg.bus_tx == GETS | req_bus_msg_reg.bus_tx == GETM);
      cache_write_request = req_bus_request & (req_bus_msg_reg.bus_tx == PUTM);
    end

    // Writeback logic
    dirty = 1'b0;

    // Calculate hit vector and data output
    ufp_rdata = 'x;
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
      if (tag_array_dout0[i][TAG_BITS-1:0] == req_bus_tag_val) begin
        // Mark as hit and set the cpu rdata correctly
        cache_hit_vector[i] = valid_array_dout0[i];
        ufp_rdata = data_array_dout0[i][({req_bus_block_offset, 3'b0})+:32];

        // Write to cache if doing a store and there is a hit
        if (write_from_cpu) begin
          tag_array_web0[i]   = 1'b0;
          data_array_web0[i]  = 1'b0;
          data_array_din0[i]  = resp_bus_msg_reg.data;
          data_array_wmask[i] = '1;

          // Mark array as valid and dirty during a write from cpu
          valid_array_din0[i] = 1'b1;
          valid_array_web0[i] = 1'b0;
          dirty_array_din0[i] = 1'b1;
        end
      end

      // Checks bus tag hits
      resp_bus_rdata = 'x;
      resp_bus_hit_vector[i] = 1'b0;
      if (tag_array_dout1[i][TAG_BITS-1:0] == resp_bus_tag_val) begin
        resp_bus_rdata = data_array_dout1[i];
        resp_bus_hit_vector[i] = valid_array_dout1[i];
      end

      // Write to cache after writeback completes
      // Only overwrite the eviction candidate
      if (write_from_mem && evict_candidate[i]) begin
        cache_hit_vector[i] = 1'b1;
        tag_array_web0[i]  = 1'b0;
        data_array_web0[i] = 1'b0;
        data_array_wmask[i] = '1;
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
          dfp_addr = {tag_array_dout0[i][TAG_BITS-1:0], req_bus_set_addr, 5'b0};
        end
      end

      // Invalidate logic
      invalidate_addr = '0;
      if (evict_candidate[i] && valid_array_dout0[i]) begin
        invalidate_addr = {tag_array_dout0[i][TAG_BITS-1:0], req_bus_set_addr, 5'b0};
      end
    end

    // Cache Hit/WB and Data Logic and
    cache_hit = |cache_hit_vector;

    // Update eviction logic when cache is replying
    evict_update = ~ufp_resp;
  end

  generate for (genvar i = 0; i < WAYS; i++) begin : gen_sram_arrays
    l2cache_data_array data_array (
      .clk0       (clk),
      .csb0       (data_array_csb0[i]),
      .web0       (data_array_web0[i]),
      .wmask0     (data_array_wmask[i]),
      .addr0      (req_bus_set_addr),
      .din0       (data_array_din0[i]),
      .dout0      (data_array_dout0[i]),
      .clk1       (clk),
      .csb1       (data_array_csb1[i]),
      .addr1      (resp_bus_set_addr),
      .dout1      (data_array_dout1[i])
    );
    l2cache_tag_array tag_array (
      .clk0       (clk),
      .csb0       (tag_array_csb0[i]),
      .web0       (tag_array_web0[i]),
      .addr0      (req_bus_set_addr),
      .din0       ({dirty_array_din0[i], req_bus_tag_val}),
      .dout0      (tag_array_dout0[i]),
      .clk1       (clk),
      .csb1       (tag_array_csb1[i]),
      .addr1      (resp_bus_set_addr),
      .dout1      (tag_array_dout1[i])
    );
    ff_array_rwr #(.WIDTH(1), .S_INDEX(SET_BITS)) valid_array (
      .clk0       (clk),
      .rst0       (rst),
      .csb0       (valid_array_csb0[i]),
      .web0       (valid_array_web0[i]),
      .addr0      (req_bus_set_addr),
      .din0       (valid_array_din0[i]),
      .dout0      (valid_array_dout0[i]),
      .clk1       (clk),
      .rst1       (rst),
      .csb1       (valid_array_csb1[i]),
      .addr1      (resp_bus_set_addr),
      .dout1      (valid_array_dout1[i])
    );
  end endgenerate

  l2cache_coherence #(
    .ID(ID),
    .WAYS(WAYS),
    .SETS(SETS)
  ) l2cache_coherence0 (
    .clk(clk),
    .rst(rst),
    .ufp_resp(ufp_resp),
    .ufp_rdata(ufp_rdata),
    .dfp_resp(dfp_resp),
    .resp_dfp_write(resp_dfp_write),
    .resp_dfp_wdata(resp_dfp_wdata),
    .cache_read_request(cache_read_request),
    .cache_write_request(cache_write_request),
    .cache_hit_vector(cache_hit_vector),
    .resp_bus_hit_vector(resp_bus_hit_vector),
    .evict_candidate(evict_candidate),
    .req_bus_msg(req_bus_msg),
    .resp_bus_msg(resp_bus_msg),
    .resp_bus_tx(resp_bus_tx),
    .resp_bus_gnt(resp_bus_gnt),
    .resp_bus_req(resp_bus_req),
    .resp_bus_busy(resp_bus_busy),
    .invalidate(invalidate),
    .invalidate_req(invalidate_req),
    .invalidate_resp(invalidate_resp),
    .invalidate_addr(invalidate_addr),
    .invalidate_done(invalidate_done)
  );

  l2cache_control #(
    .WAYS(WAYS)
  ) l2cache_control0 (
    .clk(clk),
    .rst(rst),
    .cache_hit(cache_hit),
    .cache_read_request(cache_read_request),
    .cache_write_request(cache_write_request),
    .dfp_resp(dfp_resp),
    .dfp_read(dfp_read),
    .cache_dfp_write(cache_dfp_write),
    .req_bus_request(req_bus_request),
    .tag_array_csb0(tag_array_csb0),
    .data_array_csb0(data_array_csb0),
    .valid_array_csb0(valid_array_csb0),
    .tag_array_csb1(tag_array_csb1),
    .data_array_csb1(data_array_csb1),
    .valid_array_csb1(valid_array_csb1),
    .write_from_mem(write_from_mem),
    .write_from_cpu(write_from_cpu),
    .idle(idle),
    .dirty(dirty),
    .invalidate(invalidate),
    .invalidate_done(invalidate_done)
  );

  plru #(
    .WAYS(WAYS),
    .SETS(SETS)
  ) plru0 (
    .clk(clk),
    .rst(rst),
    .evict_update(evict_update),
    .set_addr(req_bus_set_addr),
    .cache_hit_vector(cache_hit_vector),
    .evict_candidate(evict_candidate)
  );

endmodule
