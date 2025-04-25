module dcache_coherence
import cache_types::*;
#(
  parameter integer ID   = 0,
  parameter integer WAYS = 4,
  parameter integer SETS = 16
) (
  input   logic           clk,
  input   logic           rst,

  // Cache Request and Response Signals
  input  logic [31:0]     dfp_addr,
  input  logic            dfp_read,
  input  logic            dfp_write,
  input  logic [255:0]    dfp_wdata,
  output logic [255:0]    dfp_rdata,
  output logic            dfp_resp,
  input  logic [255:0]    bus_rdata,

  input  logic            cache_read_request,
  input  logic            cache_write_request,
  input  logic [WAYS-1:0] cache_hit_vector,
  input  logic [WAYS-1:0] bus_hit_vector,
  input  logic [WAYS-1:0] evict_candidate,

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

  parameter integer INDEX_WIDTH     = $clog2(SETS);
  parameter integer CACHELINE_BYTES = 32;
  parameter integer CACHELINE_BITS  = $clog2(CACHELINE_BYTES);
  parameter integer TAG_BITS        = 32 - INDEX_WIDTH - CACHELINE_BITS;

  cacheline_state_t [SETS-1:0] state_array      [WAYS];
  cacheline_state_t [SETS-1:0] state_array_next [WAYS];

  // Coherence Logic Signals
  logic                   req_bus_busy_next;
  logic                   req_bus_busy_reg;
  logic                   req_bus_req_next;
  logic                   req_bus_req_reg;
  req_msg_t               req_bus_tx_next;
  req_msg_t               req_bus_tx_reg;

  logic                   resp_bus_req_next;
  logic                   resp_bus_req_reg;
  resp_msg_t              resp_bus_tx_next;
  resp_msg_t              resp_bus_tx_reg;

  logic [INDEX_WIDTH-1:0] addr_index;
  logic [INDEX_WIDTH-1:0] req_bus_index;
  logic [INDEX_WIDTH-1:0] resp_bus_index;

  logic                   cpu_req;
  logic                   load_miss   [WAYS];
  logic                   store_miss  [WAYS];
  logic                   load_hit    [WAYS];
  logic                   store_hit   [WAYS];
  logic                   replacement [WAYS];

  // CPU Request Response Logic
  assign addr_index     = dfp_addr[INDEX_WIDTH-1:0];
  assign req_bus_index  = req_bus_msg.addr[INDEX_WIDTH-1:0];
  assign resp_bus_index = resp_bus_msg.addr[INDEX_WIDTH-1:0];

  // CPU Request Logic
  always_comb begin
    cpu_req = cache_read_request | cache_write_request;

    for (int i = 0; i < WAYS; i++) begin
      load_miss[i]   = dfp_read & evict_candidate[i];
      store_miss[i]  = dfp_write & evict_candidate[i];
      load_hit[i]    = cache_read_request & cache_hit_vector[i];
      store_hit[i]   = cache_write_request & cache_hit_vector[i];
      replacement[i] = load_miss[i] | store_miss[i];
    end
  end

  // Cacheline State Update Logic
  always_comb begin
    dfp_rdata = '0;
    state_array_next  = state_array;
    req_bus_busy_next = req_bus_busy_reg;

    // Update Cacheline State per Way
    for (int i = 0; i < WAYS; i++) begin
      // Update Cacheline State on Bus Message
      if (req_bus_msg.valid) begin
        unique case (state_array[i][req_bus_index])
          CISAD: begin
            // OwnGetS -> ISD, req_bus_busy_next = 1
            if (req_bus_msg.bus_tx == GETS && req_bus_msg.source == ID && evict_candidate[i]) begin
              state_array_next[i][req_bus_index] = CISD;
              req_bus_busy_next = '1;
            end
          end
          CIMAD: begin
            // OwnGetM -> IMD, req_bus_busy_next = 1
            if (req_bus_msg.bus_tx == GETM && req_bus_msg.source == ID && evict_candidate[i]) begin
              state_array_next[i][req_bus_index] = CIMD;
              req_bus_busy_next = '1;
            end
          end
          CS: begin
            // OtherGetM -> I
            if (req_bus_msg.bus_tx == GETM && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              state_array_next[i][req_bus_index] = CI;
            end
          end
          CSMAD: begin
            // OwnGetM -> SMD, req_bus_busy_next = 1
            if (req_bus_msg.bus_tx == GETM && req_bus_msg.source == ID && cache_hit_vector[i]) begin
              state_array_next[i][req_bus_index] = CSMD;
              req_bus_busy_next = '1;
            end
            // OtherGetM -> IMAD
            else if (req_bus_msg.bus_tx == GETM && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              state_array_next[i][req_bus_index] = CIMAD;
            end
          end
          CE: begin
            // OtherGetS -> SRD, req_bus_busy_next = 1
            if (req_bus_msg.bus_tx == GETS && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              state_array_next[i][req_bus_index] = CSRD;
              req_bus_busy_next = '1;
            end
            // OtherGetM -> IRD, req_bus_busy_next = 1
            else if (req_bus_msg.bus_tx == GETM && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              state_array_next[i][req_bus_index] = CIRD;
              req_bus_busy_next = '1;
            end
          end
          CM: begin
            // OtherGetS -> SRD, req_bus_busy_next = 1
            if (req_bus_msg.bus_tx == GETS && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              state_array_next[i][req_bus_index] = CSRD;
              req_bus_busy_next = 1;
            end
            // OtherGetM -> IRD, req_bus_busy_next = 1
            else if (req_bus_msg.bus_tx == GETM && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              state_array_next[i][req_bus_index] = CIRD;
              req_bus_busy_next = 1;
            end
          end
          CMIA: begin
            // OwnPutM -> I
            if (req_bus_msg.bus_tx == PUTM && req_bus_msg.source == ID && evict_candidate[i]) begin
              state_array_next[i][req_bus_index] = CI;
            end
            // OtherGetS -> IIARD, req_bus_busy_next = 1
            else if (req_bus_msg.bus_tx == GETS && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              state_array_next[i][req_bus_index] = CIIARD;
              req_bus_busy_next = 1;
            end
            // OtherGetM -> IIARD, req_bus_busy_next = 1
            else if (req_bus_msg.bus_tx == GETM && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              state_array_next[i][req_bus_index] = CIIARD;
              req_bus_busy_next = 1;
            end
          end
          CEIA: begin
            // OwnPutM -> I
            if (req_bus_msg.bus_tx == PUTM && req_bus_msg.source == ID && evict_candidate[i]) begin
              state_array_next[i][req_bus_index] = CI;
            end
            // OtherGetS -> IIARD, req_bus_busy_next = 1
            else if (req_bus_msg.bus_tx == GETS && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              state_array_next[i][req_bus_index] = CIIARD;
              req_bus_busy_next = 1;
            end
            // OtherGetM -> IIARD, req_bus_busy_next = 1
            else if (req_bus_msg.bus_tx == GETM && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              state_array_next[i][req_bus_index] = CIIARD;
              req_bus_busy_next = 1;
            end
          end
          CIIA: begin
            // OwnPutM -> I
            if (req_bus_msg.bus_tx == PUTM && req_bus_msg.source == ID && evict_candidate[i]) begin
              state_array_next[i][req_bus_index] = CI;
            end
          end
          // Ignore Bus Requests for CI, CISD, CIMD, CIRD, CSMD, CSRD, CIIARD
          default: begin
          end
        endcase
      end
      // Update Cacheline State on Response Bus
      else if (resp_bus_msg.valid) begin
        unique case (state_array[i][resp_bus_index])
          CISD: begin
            // Data Response -> S, req_bus_busy_next = 0
            if (resp_bus_msg.mmsg == DATA && resp_bus_msg.destination == ID && evict_candidate[i]) begin
              state_array_next[i][resp_bus_index] = CS;
              dfp_rdata = resp_bus_msg.data;
              req_bus_busy_next = '0;
            end
            // Exclusive Data Response -> E, req_bus_busy_next = 0
            else if (resp_bus_msg.mmsg == EXCLUSIVE && resp_bus_msg.destination == ID && evict_candidate[i]) begin
              state_array_next[i][resp_bus_index] = CE;
              dfp_rdata = resp_bus_msg.data;
              req_bus_busy_next = '0;
            end
          end
          CIMD: begin
            // Data Response -> M, req_bus_busy_next = 0
            if (resp_bus_msg.mmsg == DATA && resp_bus_msg.destination == ID && evict_candidate[i]) begin
              state_array_next[i][resp_bus_index] = CM;
              dfp_rdata = resp_bus_msg.data;
              req_bus_busy_next = '0;
            end
          end
          CIRD: begin
            // Own Data Response -> I, req_bus_busy_next = 0
            if (resp_bus_msg.source == ID && resp_bus_msg.way == i) begin
              state_array_next[i][resp_bus_index] = CI;
              req_bus_busy_next = '0;
            end
          end
          CSMD: begin
            // Data Response -> M, req_bus_busy_next = 0
            if (resp_bus_msg.mmsg == DATA && resp_bus_msg.destination == ID && cache_hit_vector[i]) begin
              state_array_next[i][resp_bus_index] = CM;
              dfp_rdata = resp_bus_msg.data;
              req_bus_busy_next = '0;
            end
          end
          CSRD: begin
            // Own Data Response -> S, req_bus_busy_next = 0
            if (resp_bus_msg.source == ID && resp_bus_msg.way == i) begin
              state_array_next[i][resp_bus_index] = CS;
              req_bus_busy_next = '0;
            end
          end
          CIIARD: begin
            // Own Data Response -> IIA, req_bus_busy_next = 0
            if (resp_bus_msg.source == ID && resp_bus_msg.way == i) begin
              state_array_next[i][resp_bus_index] = CIIA;
              req_bus_busy_next = '0;
            end
          end
          // Ignore Bus Requests for CI, CISAD, CIMAD, CS, CSMAD, CE, CM, CMIA, CEIA, CIIA
          default: begin
          end
        endcase
      end
      // Update Cacheline State on CPU Request
      else if (cpu_req) begin
        unique case (state_array[i][addr_index])
          CI: begin
            // load -> ISAD
            if (load_miss[i]) begin
              state_array_next[i][addr_index] = CISAD;
            end
            // store -> IMAD
            else if (store_miss[i]) begin
              state_array_next[i][addr_index] = CIMAD;
            end
          end
          CS: begin
            // store -> SMAD
            if (store_hit[i]) begin
              state_array_next[i][addr_index] = CSMAD;
            end
            // replacement -> I
            else if (replacement[i]) begin
              state_array_next[i][addr_index] = CI;
            end
          end
          CE: begin
            // store -> M
            if (store_hit[i]) begin
              state_array_next[i][addr_index] = CM;
            end
            // replacement -> EIA
            else if (replacement[i]) begin
              state_array_next[i][addr_index] = CEIA;
            end
          end
          CM: begin
            // replacement -> MIA
            if (replacement[i]) begin
              state_array_next[i][addr_index] = CMIA;
            end
          end
          // Ignore Bus Requests for CISAD, CISD, CIMAD, CIMD, CIRD, CSMAD, CSMD, CSRD, CMIA, CEIA, CIIA, CIIARD
          default: begin
          end
        endcase
      end

      // CPU Request Update Logic
      if (cpu_req) begin
        unique case (cacheline[i][addr_index].state)
          CS, CSMAD, CSMD, CEIA: begin
            // load -> hit
            if (load_hit[i]) begin
              dfp_resp = '1;
            end
          end
          CE, CM, CMIA: begin
            // load -> hit
            if (load_hit[i]) begin
              dfp_resp = '1;
            end
            // store -> hit
            else if (store_hit[i]) begin
              dfp_resp = '1;
            end
          end
          // Ignore Bus Requests for CI, CISAD, CISD, CIMAD, CIMD, CIRD, CSRD, CIIA, CIIARD
          default: begin
          end
        endcase
      end
    end
  end

  assign req_bus_busy = req_bus_busy_next | req_bus_busy_reg;

  // Request Bus Output Logic
  always_comb begin
    req_bus_req_next = req_bus_req_reg;
    req_bus_tx_next  = req_bus_tx_reg;

    for (int i = 0; i < WAYS; i++) begin
      if (cpu_req) begin
        unique case (state_array[i][addr_index])
          CI: begin
            // load -> Issue GetS, req_bus_req_next = 1
            if (load_miss[i]) begin
              req_bus_req_next = '1;
              req_bus_tx_next = '{
                valid: '1,
                source: ID,
                addr: dfp_addr,
                bus_tx: GETS
              };
            end
            // store -> Issue GetM, req_bus_req_next = 1
            else if (store_miss[i]) begin
              req_bus_req_next = '1;
              req_bus_tx_next = '{
                valid: '1,
                source: ID,
                addr: dfp_addr,
                bus_tx: GETM
              };
            end
          end
          CISAD: begin
            // OwnGetS -> req_bus_req_next = 0
            if (req_bus_msg.valid && req_bus_msg.bus_tx == GETS && req_bus_msg.source == ID) begin
              req_bus_req_next = '0;
              req_bus_tx_next = '{
                valid: '0,
                source: ID,
                addr: '0,
                bus_tx: NONE
              };
            end
          end
          CIMAD, CSMAD: begin
            // OwnGetM -> req_bus_req_next = 0
            if (req_bus_msg.valid && req_bus_msg.bus_tx == GETM && req_bus_msg.source == ID) begin
              req_bus_req_next = '0;
              req_bus_tx_next = '{
                valid: '0,
                source: ID,
                addr: '0,
                bus_tx: NONE
              };
            end
          end
          CMIA, CEIA, CIIA: begin
            // OwnPutM -> req_bus_req_next = 0
            if (req_bus_msg.valid && req_bus_msg.bus_tx == PUTM && req_bus_msg.source == ID) begin
              req_bus_req_next = '0;
              req_bus_tx_next = '{
                valid: '0,
                source: ID,
                addr: '0,
                bus_tx: NONE
              };
            end
          end
          CS: begin
            // store -> issue GetM, req_bus_req_next = 1
            if (store_hit[i]) begin
              req_bus_req_next = '1;
              req_bus_tx_next = '{
                valid: '1,
                source: ID,
                addr: dfp_addr,
                bus_tx: GETM
              };
            end
          end
          CE, CM: begin
            // replacement -> Issue PutM, req_bus_req_next = 1
            if (replacement[i]) begin
              req_bus_req_next = '1;
              req_bus_tx_next = '{
                valid: '1,
                source: ID,
                addr: dfp_addr,
                bus_tx: PUTM
              };
            end
          end
          // Ignore Bus Requests for CISD, CIMD, CIRD, CSRD, CSMD, CIIARD
          default: begin
          end
        endcase
      end
    end
  end

  assign req_bus_req = req_bus_req_next;
  assign req_bus_tx  = req_bus_tx_next;

  // Response Bus Output Logic
  always_comb begin
    resp_bus_req_next = resp_bus_req_reg;
    resp_bus_tx_next = resp_bus_tx_reg;

    for (int i = 0; i < WAYS; i++) begin
      if (req_bus_msg.valid) begin
        unique case (state_array[i][req_bus_index])
          CE, CM: begin
            // OtherGetS -> Send Data to Bus Source & Memory, req_bus_req_next = 1
            if (req_bus_msg.bus_tx == GETS && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              resp_bus_req_next = '1;
              resp_bus_tx_next = '{
                valid: '1,
                source: ID,
                way: i,
                destination: req_bus_msg.source,
                memory_flag: '1,
                addr: req_bus_msg.addr,
                data: bus_rdata,
                mmsg: DATA
              };
            end
            // OtherGetM -> Send Data to Bus Source, req_bus_req_next = 1
            else if (req_bus_msg.bus_tx == GETM && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              resp_bus_req_next = '1;
              resp_bus_tx_next = '{
                valid: '1,
                source: ID,
                way: i,
                destination: req_bus_msg.source,
                memory_flag: '0,
                addr: req_bus_msg.addr,
                data: bus_rdata,
                mmsg: DATA
              };
            end
          end
          CMIA: begin
            // OwnPutM -> Send Data to Memory, req_bus_req_next = 1
            if (req_bus_msg.bus_tx == PUTM && req_bus_msg.source == ID) begin
              resp_bus_req_next = '1;
              resp_bus_tx_next = '{
                valid: '1,
                source: ID,
                way: i,
                destination: NUM_CACHE,
                memory_flag: '1,
                addr: req_bus_msg.addr,
                data: bus_rdata,
                mmsg: DATA
              };
            end
            // OtherGetS -> Send Data to Bus Source & Memory, req_bus_req_next = 1
            else if (req_bus_msg.bus_tx == GETS && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              resp_bus_req_next = '1;
              resp_bus_tx_next = '{
                valid: '1,
                source: ID,
                way: i,
                destination: req_bus_msg.source,
                memory_flag: '1,
                addr: req_bus_msg.addr,
                data: bus_rdata,
                mmsg: DATA
              };
            end
            // OtherGetM -> Send Data to Bus Source, req_bus_req_next = 1
            else if (req_bus_msg.bus_tx == GETM && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              resp_bus_req_next = '1;
              resp_bus_tx_next = '{
                valid: '1,
                source: ID,
                way: i,
                destination: req_bus_msg.source,
                memory_flag: '0,
                addr: req_bus_msg.addr,
                data: bus_rdata,
                mmsg: DATA
              };
            end
          end
          CEIA: begin
            // OwnPutM -> Send NoDataE to Memory, req_bus_req_next = 1
            if (req_bus_msg.bus_tx == PUTM && req_bus_msg.source == ID) begin
              resp_bus_req_next = '1;
              resp_bus_tx_next = '{
                valid: '1,
                source: ID,
                way: i,
                destination: NUM_CACHE,
                memory_flag: '1,
                addr: req_bus_msg.addr,
                data: bus_rdata,
                mmsg: NODATAE
              };
            end
            // OtherGetS -> Send Data to Bus Source & Memory, req_bus_req_next = 1
            else if (req_bus_msg.bus_tx == GETS && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              resp_bus_req_next = '1;
              resp_bus_tx_next = '{
                valid: '1,
                source: ID,
                way: i,
                destination: req_bus_msg.source,
                memory_flag: '1,
                addr: req_bus_msg.addr,
                data: bus_rdata,
                mmsg: DATA
              };
            end
            // OtherGetM -> Send Data to Bus Source, req_bus_req_next = 1
            else if (req_bus_msg.bus_tx == GETM && req_bus_msg.source != ID && bus_hit_vector[i]) begin
              resp_bus_req_next = '1;
              resp_bus_tx_next = '{
                valid: '1,
                source: ID,
                way: i,
                destination: req_bus_msg.source,
                memory_flag: '0,
                addr: req_bus_msg.addr,
                data: bus_rdata,
                mmsg: DATA
              };
            end
          end
          CIIA: begin
            // OwnPutM -> Send NoData to Memory, req_bus_req_next = 1
            if (req_bus_msg.bus_tx == PUTM && req_bus_msg.source == ID) begin
              resp_bus_req_next = '1;
              resp_bus_tx_next = '{
                valid: '1,
                source: ID,
                way: i,
                destination: NUM_CACHE,
                memory_flag: '1,
                addr: req_bus_msg.addr,
                data: bus_rdata,
                mmsg: NODATA
              };
            end
          end
          // Ignore Bus Requests for CI, CISAD, CISD, CIMAD, CIMD, CIRD CS, CSMAD, CSMD, CSRD, CIIARD
          default: begin
          end
        endcase
      end
      else if (resp_bus_msg.valid) begin
        unique case (state_array[i][resp_bus_index])
          CIRD: begin
            // Own Data Response -> req_bus_req_next = 0
            if (resp_bus_msg.source == ID && resp_bus_msg.way == i) begin
              resp_bus_req_next = '0;
              resp_bus_tx_next = '{
                valid: '0,
                source: ID,
                way: i,
                destination: ID,
                memory_flag: '0,
                addr: '0,
                data: '0,
                mmsg: NODATA
              };
            end
          end
          CSRD: begin
            // Own Data Response -> req_bus_req_next = 0
            if (resp_bus_msg.source == ID && resp_bus_msg.way == i) begin
              resp_bus_req_next = '0;
              resp_bus_tx_next = '{
                valid: '0,
                source: ID,
                way: i,
                destination: ID,
                memory_flag: '0,
                addr: '0,
                data: '0,
                mmsg: NODATA
              };
            end
          end
          CIIARD: begin
            // Own Data Response -> req_bus_req_next = 0
            if (resp_bus_msg.source == ID && resp_bus_msg.way == i) begin
              resp_bus_req_next = '0;
              resp_bus_tx_next = '{
                valid: '0,
                source: ID,
                way: i,
                destination: ID,
                memory_flag: '0,
                addr: '0,
                data: '0,
                mmsg: NODATA
              };
            end
          end
          // Ignore Bus Requests for CI, CISAD, CISD, CIMAD, CIMD, CS, CSMAD, CSMD, CE, CM, CMIA, CEIA, CIIA,
          default: begin
          end
        endcase
      end
    end
  end

  assign resp_bus_req  = req_bus_req_next;
  assign resp_bus_tx   = req_bus_tx_next;

  // Cache logic
  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 0; i < WAYS; i++) begin
        state_array[i] <= '{default: CI};
      end

      req_bus_busy_reg <= '0;
      req_bus_req_reg  <= '0;
      req_bus_tx_reg   <= '0;
      resp_bus_req_reg <= '0;
      resp_bus_tx_reg  <= '0;
    end
    else begin
      for (int i = 0; i < WAYS; i++) begin
        state_array[i] <= state_array_next[i];
      end

      req_bus_busy_reg <= req_bus_busy_next;
      req_bus_req_reg  <= req_bus_req_next;
      req_bus_tx_reg   <= req_bus_tx_next;
      resp_bus_req_reg <= resp_bus_req_next;
      resp_bus_tx_reg  <= resp_bus_tx_next;
    end
  end

endmodule
