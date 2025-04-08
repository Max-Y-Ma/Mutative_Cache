module cache
import types::*;
#(
  parameter integer ID
)
(
  input   logic                                   clk,
  input   logic                                   rst,

  // From CPU
  input   logic                                   cpu_req,
  input   logic                                   cpu_we,
  input   logic       [XLEN-1:0]                  cpu_addr,
  input   logic       [CACHELINE_SIZE-1:0]        cpu_wdata,

  // To CPU
  output  logic                                   cpu_ready,
  output  logic                                   cpu_resp,
  output  logic       [CACHELINE_SIZE-1:0]        cpu_rdata,

  // From Snoop Bus
  input   bus_msg_t                               bus_msg,

  // To Snoop Bus
  output  logic       [XLEN-1:0]                  bus_addr,
  output  bus_tx_t                                bus_tx,

  // To Arbiter
  output  logic                                   arbiter_req,
  output  logic                                   arbiter_busy,

  // From Arbiter
  input   logic                                   arbiter_gnt,

  // To Xbar
  output  xbar_msg_t                              xbar_out,

  // From Xbar
  input   xbar_msg_t                              xbar_in[NUM_CPUS]
);

  cacheline_t cacheline      [NUM_SETS];
  cacheline_t cacheline_next [NUM_SETS];

  logic                   hit;
  logic                   bus_hit;
  logic                   load;
  logic                   store;
  logic                   replacement;
  logic                   arbiter_busy_next;
  logic                   arbiter_busy_reg;
  logic                   arbiter_req_next;
  logic                   arbiter_req_reg;
  logic [INDEX_WIDTH-1:0] addr_index;
  logic [TAG_WIDTH-1:0]   addr_tag;

  logic [INDEX_WIDTH-1:0]      xbar_index;
  logic [TAG_WIDTH-1:0]        xbar_tag;
  logic [INDEX_WIDTH-1:0]      bus_msg_index;
  logic [TAG_WIDTH-1:0]        bus_msg_tag;
  logic                        xbar_msg_valid;
  logic [$clog2(NUM_CPUS)-1:0] xbar_idx;

  logic    [XLEN-1:0] bus_addr_reg;
  bus_tx_t            bus_tx_reg;

  // Xbar input logic
  always_comb begin
    xbar_msg_valid  = '0;
    xbar_idx        = '0;
    for (int i = 0; i < NUM_CPUS; i++) begin
      if (xbar_in[i].valid && xbar_in[i].destination == ID) begin
        xbar_msg_valid = '1;
        xbar_idx       = ($clog2(NUM_CPUS))'(i);
      end
    end
  end

  // Xbar output logic
  always_ff @(posedge clk) begin
    if (rst) begin
      xbar_out <= '{
        valid: '0,
        destination: '0,
        memory_flag: '0,
        addr: '0,
        data: '0,
        mmsg: '0
      };
    end else begin
      xbar_out <= '0;

      if (bus_msg.valid) begin
        unique case (cacheline[bus_msg_index].state)
          CE, CM: begin
            // OtherGetS -> Send Data to Bus Source & Memory
            if (bus_msg.bus_tx == GETS && bus_msg.source != ID && bus_hit) begin
              xbar_out <= '{
                valid: '1,
                destination: bus_msg.source,
                memory_flag: '1,
                addr: bus_msg.addr,
                data: cacheline[bus_msg_index].data,
                mmsg: DATA
              };
            end
            // OtherGetM -> Send Data to Bus Source
            else if (bus_msg.bus_tx == GETM && bus_msg.source != ID && bus_hit) begin
              xbar_out <= '{
                valid: '1,
                destination: bus_msg.source,
                memory_flag: '0,
                addr: bus_msg.addr,
                data: cacheline[bus_msg_index].data,
                mmsg: DATA
              };
            end
          end
          CMIA: begin
            // OwnPutM -> Send Data to Memory
            if (bus_msg.bus_tx == PUTM && bus_msg.source == ID) begin
              xbar_out <= '{
                valid: '0,
                destination: NUM_CPUS,
                memory_flag: '1,
                addr: bus_msg.addr,
                data: cacheline[bus_msg_index].data,
                mmsg: DATA
              };
            end
            // OtherGetS -> Send Data to Bus Source & Memory
            else if (bus_msg.bus_tx == GETS && bus_msg.source != ID && bus_hit) begin
              xbar_out <= '{
                valid: '1,
                destination: bus_msg.source,
                memory_flag: '1,
                addr: bus_msg.addr,
                data: cacheline[bus_msg_index].data,
                mmsg: DATA
              };
            end
            // OtherGetM -> Send Data to Bus Source
            else if (bus_msg.bus_tx == GETM && bus_msg.source != ID && bus_hit) begin
              xbar_out <= '{
                valid: '1,
                destination: bus_msg.source,
                memory_flag: '0,
                addr: bus_msg.addr,
                data: cacheline[bus_msg_index].data,
                mmsg: DATA
              };
            end
          end
          CEIA: begin
            // OwnPutM -> Send NoDataE to Memory
            if (bus_msg.bus_tx == PUTM && bus_msg.source == ID) begin
              xbar_out <= '{
                valid: '0,
                destination: NUM_CPUS,
                memory_flag: '1,
                addr: bus_msg.addr,
                data: cacheline[bus_msg_index].data,
                mmsg: NODATAE
              };
            end
            // OtherGetS -> Send Data to Bus Source & Memory
            else if (bus_msg.bus_tx == GETS && bus_msg.source != ID && bus_hit) begin
              xbar_out <= '{
                valid: '1,
                destination: bus_msg.source,
                memory_flag: '1,
                addr: bus_msg.addr,
                data: cacheline[bus_msg_index].data,
                mmsg: DATA
              };
            end
            // OtherGetM -> Send Data to Bus Source
            else if (bus_msg.bus_tx == GETM && bus_msg.source != ID && bus_hit) begin
              xbar_out <= '{
                valid: '1,
                destination: bus_msg.source,
                memory_flag: '0,
                addr: bus_msg.addr,
                data: cacheline[bus_msg_index].data,
                mmsg: DATA
              };
            end
          end
          CIIA: begin
            // OwnPutM -> Send NoData to Memory
            if (bus_msg.bus_tx == PUTM && bus_msg.source == ID) begin
              xbar_out <= '{
                valid: '0,
                destination: NUM_CPUS,
                memory_flag: '1,
                addr: bus_msg.addr,
                data: cacheline[bus_msg_index].data,
                mmsg: NODATA
              };
            end
          end
          // Ignore Bus Requests for CI, CISAD, CISD, CIMAD, CIMD, CS, CSMAD, CSMD
          default: begin
          end
        endcase
      end
    end
  end

  // CPU Request Response Logic
  assign addr_index    = cpu_addr[INDEX_WIDTH-1:0];
  assign addr_tag      = cpu_addr[XLEN-1:INDEX_WIDTH];
  assign xbar_index    = xbar_in[xbar_idx].addr[INDEX_WIDTH-1:0];
  assign xbar_tag      = xbar_in[xbar_idx].addr[XLEN-1:INDEX_WIDTH];
  assign bus_msg_index = bus_msg.addr[INDEX_WIDTH-1:0];
  assign bus_msg_tag   = bus_msg.addr[XLEN-1:INDEX_WIDTH];
  assign hit           = cacheline[addr_index].tag == addr_tag;
  assign bus_hit       = cacheline[bus_msg_index].tag == bus_msg_tag;

  assign load        = cpu_req & ~cpu_we;
  assign store       = cpu_req & cpu_we;
  assign replacement = cpu_req & ~hit;

  // Cacheline State Update Logic
  always_comb begin
    cpu_resp  = '0;
    cpu_rdata = '0;
    cacheline_next    = cacheline;
    arbiter_busy_next = arbiter_busy_reg;

    // Update Cacheline State on Bus Message
    if (bus_msg.valid) begin
      unique case (cacheline[bus_msg_index].state)
        CISAD: begin
          // OwnGetS -> ISD, arbiter_busy_next = 1
          if (bus_msg.bus_tx == GETS && bus_msg.source == ID) begin
            cacheline_next[bus_msg_index].state = CISD;
            arbiter_busy_next = '1;
          end
        end
        CIMAD: begin
          // OwnGetM -> IMD, arbiter_busy_next = 1
          if (bus_msg.bus_tx == GETM && bus_msg.source == ID) begin
            cacheline_next[bus_msg_index].state = CIMD;
            arbiter_busy_next = '1;
          end
        end
        CS: begin
          // OtherGetM -> I
          if (bus_msg.bus_tx == GETM && bus_msg.source != ID && bus_hit) begin
            cacheline_next[bus_msg_index].state = CI;
          end
        end
        CSMAD: begin
          // OwnGetM -> SMD, arbiter_busy_next = 1
          if (bus_msg.bus_tx == GETM && bus_msg.source == ID) begin
            cacheline_next[bus_msg_index].state = CSMD;
            arbiter_busy_next = '1;
          end
          // OtherGetM -> IMAD
          else if (bus_msg.bus_tx == GETM && bus_msg.source != ID && bus_hit) begin
            cacheline_next[bus_msg_index].state = CIMAD;
          end
        end
        CE: begin
          // OtherGetS -> S
          if (bus_msg.bus_tx == GETS && bus_msg.source != ID && bus_hit) begin
            cacheline_next[bus_msg_index].state = CS;
          end
          // OtherGetM -> I
          else if (bus_msg.bus_tx == GETM && bus_msg.source != ID && bus_hit) begin
            cacheline_next[bus_msg_index].state = CI;
          end
        end
        CM: begin
          // OtherGetS -> S
          if (bus_msg.bus_tx == GETS && bus_msg.source != ID && bus_hit) begin
            cacheline_next[bus_msg_index].state = CS;
          end
          // OtherGetM -> I
          else if (bus_msg.bus_tx == GETM && bus_msg.source != ID && bus_hit) begin
            cacheline_next[bus_msg_index].state = CI;
          end
        end
        CMIA: begin
          // OwnPutM -> I
          if (bus_msg.bus_tx == PUTM && bus_msg.source == ID) begin
            cacheline_next[bus_msg_index].state = CI;
          end
          // OtherGetS -> IIA
          else if (bus_msg.bus_tx == GETS && bus_msg.source != ID && bus_hit) begin
            cacheline_next[bus_msg_index].state = CIIA;
          end
          // OtherGetM -> IIA
          else if (bus_msg.bus_tx == GETM && bus_msg.source != ID && bus_hit) begin
            cacheline_next[bus_msg_index].state = CIIA;
          end
        end
        CEIA: begin
          // OwnPutM -> I
          if (bus_msg.bus_tx == PUTM && bus_msg.source == ID) begin
            cacheline_next[bus_msg_index].state = CI;
          end
          // OtherGetS -> IIA
          else if (bus_msg.bus_tx == GETS && bus_msg.source != ID && bus_hit) begin
            cacheline_next[bus_msg_index].state = CIIA;
          end
          // OtherGetM -> IIA
          else if (bus_msg.bus_tx == GETM && bus_msg.source != ID && bus_hit) begin
            cacheline_next[bus_msg_index].state = CIIA;
          end
        end
        CIIA: begin
          // OwnPutM -> I
          if (bus_msg.bus_tx == PUTM && bus_msg.source == ID) begin
            cacheline_next[bus_msg_index].state = CI;
          end
        end
        // Ignore Bus Requests for CI, CISD, CIMD, CSMD
        default: begin
        end
      endcase
    end
    // Update Cacheline State on Xbar Response
    else if (xbar_msg_valid) begin
      unique case (cacheline[xbar_index].state)
        CISD: begin
          // Own Data Response -> S, Update Cacheline, arbiter_busy_next = 0
          if (xbar_in[xbar_idx].mmsg == DATA) begin
            cacheline_next[xbar_index].state = CS;
            cacheline_next[xbar_index].data = xbar_in[xbar_idx].data;
            cacheline_next[xbar_index].tag = xbar_tag;
            arbiter_busy_next = '0;
          end
          // Own Data Response -> E, Update Cacheline, arbiter_busy_next = 0
          else if (xbar_in[xbar_idx].mmsg == EXCLUSIVE) begin
            cacheline_next[xbar_index].state = CE;
            cacheline_next[xbar_index].data = xbar_in[xbar_idx].data;
            cacheline_next[xbar_index].tag = xbar_tag;
            arbiter_busy_next = '0;
          end
        end
        CIMD: begin
          // Own Data Response -> M, Update Cacheline, arbiter_busy_next = 0
          if (xbar_in[xbar_idx].mmsg == DATA) begin
            cacheline_next[xbar_index].state = CM;
            cacheline_next[xbar_index].data = xbar_in[xbar_idx].data;
            cacheline_next[xbar_index].tag = xbar_tag;
            arbiter_busy_next = '0;
          end
        end
        CSMD: begin
          // Own Data Response -> M, Update Cacheline, arbiter_busy_next = 0
          if (xbar_in[xbar_idx].mmsg == DATA) begin
            cacheline_next[xbar_index].state = CM;
            cacheline_next[xbar_index].data = xbar_in[xbar_idx].data;
            cacheline_next[xbar_index].tag = xbar_tag;
            arbiter_busy_next = '0;
          end
        end
        // Ignore Bus Requests for CI, CISAD, CIMAD, CS, CSMAD, CE, CM, CMIA, CEIA, CIIA
        default: begin
        end
      endcase
    end
    // Update Cacheline State on CPU Request
    else if (cpu_req) begin
      unique case (cacheline[addr_index].state)
        CI: begin
          // load -> ISAD
          if (load) begin
            cacheline_next[addr_index].state = CISAD;
          end
          // store -> IMAD
          else if (store) begin
            cacheline_next[addr_index].state = CIMAD;
          end
        end
        CS: begin
          // store -> SMAD
          if (store && hit) begin
            cacheline_next[addr_index].state = CSMAD;
          end
          // replacement -> I
          else if (replacement) begin
            cacheline_next[addr_index].state = CI;
          end
        end
        CE: begin
          // store -> M
          if (store && hit) begin
            cacheline_next[addr_index].state = CM;
          end
          // replacement -> EIA
          else if (replacement) begin
            cacheline_next[addr_index].state = CEIA;
          end
        end
        CM: begin
          // replacement -> MIA
          if (replacement) begin
            cacheline_next[addr_index].state = CMIA;
          end
        end
        // Ignore Bus Requests for CISAD, CISD, CIMAD, CIMD, CSMAD, CSMD, CMIA, CEIA, CIIA
        default: begin
        end
      endcase
    end

    // CPU Request Update Logic
    if (cpu_req) begin
      unique case (cacheline[addr_index].state)
        CS, CSMAD, CSMD, CEIA: begin
          // load -> hit
          if (load && hit) begin
            cpu_resp = '1;
            cpu_rdata = cacheline[addr_index].data;
          end
        end
        CE, CM, CMIA: begin
          // load -> hit
          if (load && hit) begin
            cpu_resp = '1;
            cpu_rdata = cacheline[addr_index].data;
          end
          // store -> hit
          else if (store && hit) begin
            cpu_resp = '1;
            cacheline_next[addr_index].data = cpu_wdata;
          end
        end
        // Ignore Bus Requests for CI, CISAD, CISD, CIMAD, CIMD, CIIA
        default: begin
        end
      endcase
    end
  end

  assign arbiter_busy = arbiter_busy_next | arbiter_busy_reg;

  // Bus Output Logic
  always_comb begin
    bus_addr = bus_addr_reg;
    bus_tx   = bus_tx_reg;

    arbiter_req_next = arbiter_req_reg;

    if (cpu_req) begin
      unique case (cacheline[addr_index].state)
        CI: begin
          // load -> Issue GetS, arbiter_req_next = 1
          if (load) begin
            bus_addr = cpu_addr;
            bus_tx = GETS;
            arbiter_req_next = '1;
          end
          // store -> Issue GetM, arbiter_req_next = 1
          else if (store) begin
            bus_addr = cpu_addr;
            bus_tx = GETM;
            arbiter_req_next = '1;
          end
        end
        CISAD: begin
          // OwnGetS -> arbiter_req_next = 0
          if (bus_msg.valid && bus_msg.bus_tx == GETS && bus_msg.source == ID) begin
            arbiter_req_next = '0;
            bus_addr = '0;
            bus_tx   = IDLE;
          end
        end
        CIMAD, CSMAD: begin
          // OwnGetM -> arbiter_req_next = 0
          if (bus_msg.valid && bus_msg.bus_tx == GETM && bus_msg.source == ID) begin
            arbiter_req_next = '0;
            bus_addr = '0;
            bus_tx   = IDLE;
          end
        end
        CMIA, CEIA, CIIA: begin
          // OwnPutM -> arbiter_req_next = 0
          if (bus_msg.valid && bus_msg.bus_tx == PUTM && bus_msg.source == ID) begin
            arbiter_req_next = '0;
            bus_addr = '0;
            bus_tx   = IDLE;
          end
        end
        CS: begin
          // store -> issue GetM, arbiter_req = 1
          if (store && hit) begin
            bus_addr = cpu_addr;
            bus_tx = GETM;
            arbiter_req_next = '1;
          end
        end
        CE, CM: begin
          // replacement -> Issue PutM, arbiter_req = 1
          if (replacement) begin
            bus_addr = {cacheline[addr_index].tag, addr_index};
            bus_tx = PUTM;
            arbiter_req_next = '1;
          end
        end
        // Ignore Bus Requests for CISD, CIMD, CSMD
        default: begin
        end
      endcase
    end
  end

  assign arbiter_req = arbiter_req_next;

  // Cache logic
  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 0; i < NUM_SETS; i++) begin
        cacheline[i] <= '{
          state: CI,
          data: 0,
          tag: 0
        };
      end
      cpu_ready        <= '1;
      arbiter_busy_reg <= '0;
      arbiter_req_reg  <= '0;
      bus_addr_reg     <= '0;
      bus_tx_reg       <= '0;
    end else begin
      for (int i = 0; i < NUM_SETS; i++) begin
        cacheline[i] <= cacheline_next[i];
      end

      if (cpu_req) begin
        cpu_ready <= '0;
      end
      if (cpu_resp) begin
        cpu_ready <= '1;
      end

      arbiter_busy_reg <= arbiter_busy_next;
      arbiter_req_reg  <= arbiter_req_next;
      bus_addr_reg     <= bus_addr;
      bus_tx_reg       <= bus_tx;
    end
  end

  // Check all cacheline states have been reached for each set
  for (genvar i = 0; i < NUM_SETS; i++) begin : gen_cacheline_states
    cover_cacheline_states_CI: cover property(@(posedge clk) cacheline[i].state == CI);
    cover_cacheline_states_CISAD: cover property(@(posedge clk) cacheline[i].state == CISAD);
    cover_cacheline_states_CISD: cover property(@(posedge clk) cacheline[i].state == CISD);
    cover_cacheline_states_CIMAD: cover property(@(posedge clk) cacheline[i].state == CIMAD);
    cover_cacheline_states_CIMD: cover property(@(posedge clk) cacheline[i].state == CIMD);
    cover_cacheline_states_CS: cover property(@(posedge clk) cacheline[i].state == CS);
    cover_cacheline_states_CSMAD: cover property(@(posedge clk) cacheline[i].state == CSMAD);
    cover_cacheline_states_CSMD: cover property(@(posedge clk) cacheline[i].state == CSMD);
    cover_cacheline_states_CE: cover property(@(posedge clk) cacheline[i].state == CE);
    cover_cacheline_states_CM: cover property(@(posedge clk) cacheline[i].state == CM);
    cover_cacheline_states_CMIA: cover property(@(posedge clk) cacheline[i].state == CMIA);
    cover_cacheline_states_CEIA: cover property(@(posedge clk) cacheline[i].state == CEIA);
    cover_cacheline_states_CIIA: cover property(@(posedge clk) cacheline[i].state == CIIA);
  end

  // Check that if a OwnGetM is on the bus, that cacheline eventually reaches modified
  // Check that if a OtherGetM is on the bus, this cacheline eventually reaches invalid
  logic [INDEX_WIDTH-1:0] bus_index1;
  logic [INDEX_WIDTH-1:0] bus_index2;
  always_ff @(posedge clk) begin
    if (bus_msg.valid && bus_msg.bus_tx == GETM && bus_msg.source == ID) begin
      bus_index1 <= bus_msg.addr[INDEX_WIDTH-1:0];
    end

    if (bus_msg.valid && bus_msg.bus_tx == GETM && bus_msg.source != ID && bus_hit) begin
      bus_index2 <= bus_msg.addr[INDEX_WIDTH-1:0];
    end
  end

  property p_owngetm_modified;
    @(posedge clk) disable iff (rst)
    $rose(bus_msg.valid && bus_msg.bus_tx == GETM && bus_msg.source == ID)
    |-> s_eventually (cacheline[bus_index1].state == CM);
  endproperty

  assert property (p_owngetm_modified) else
  $error("ERROR: Cacheline state did not reach modified after OwnGetM!");

  property p_othergetm_invalid;
    @(posedge clk) disable iff (rst)
    $rose(bus_msg.valid && bus_msg.bus_tx == GETM && bus_msg.source != ID && bus_hit)
    |-> s_eventually (cacheline[bus_index2].state == CI);
  endproperty

  assert property (p_othergetm_invalid) else
  $error("ERROR: Cacheline state did not reach invalid after OtherGetM!");

  // Check that if a OwnGetS is on the bus, that cacheline eventually reaches shared or exclusive
  logic [INDEX_WIDTH-1:0] bus_index3;
  always_ff @(posedge clk) begin
    if (bus_msg.valid && bus_msg.bus_tx == GETS && bus_msg.source == ID) begin
      bus_index3 <= bus_msg.addr[INDEX_WIDTH-1:0];
    end
  end

  property p_owngets_shared_exclusive;
    @(posedge clk) disable iff (rst)
    $rose(bus_msg.valid && bus_msg.bus_tx == GETS && bus_msg.source == ID)
    |-> s_eventually (cacheline[bus_index3].state == CS || cacheline[bus_index3].state == CE);
  endproperty

  assert property (p_owngets_shared_exclusive) else
  $error("ERROR: Cacheline state did not reach shared after OwnGetS!");

  // Check that cpu_resp is eventually asserted after a cpu_req
  property p_cpu_resp_after_cpu_req;
    @(posedge clk) disable iff (rst)
    $rose(cpu_req) |-> s_eventually (cpu_resp);
  endproperty

  assert property (p_cpu_resp_after_cpu_req) else $error("ERROR: cpu_resp never occured!");

  // Check that cpu_ready is evenutally asserted after a cpu_resp
  property p_cpu_ready_after_cpu_resp;
    @(posedge clk) disable iff (rst)
    $rose(cpu_resp) |-> s_eventually (cpu_ready);
  endproperty

  assert property (p_cpu_ready_after_cpu_resp) else $error("ERROR: cpu_ready never occured!");

  // Check that if an arbiter_req is asserted, an arbiter_gnt is eventually recieved
  property p_arbiter_gnt_after_req;
    @(posedge clk) disable iff (rst)
    $rose(arbiter_req) |-> s_eventually (arbiter_gnt);
  endproperty

  assert property (p_arbiter_gnt_after_req) else $error("ERROR: arbiter_gnt never occured!");

  // Check that arbiter_busy is asserted in atomic states
  property p_arbiter_busy_atomic;
    @(posedge clk) disable iff (rst)
    (
      cacheline[cpu_addr[INDEX_WIDTH-1:0]].state == CISD ||
      cacheline[cpu_addr[INDEX_WIDTH-1:0]].state == CIMD ||
      cacheline[cpu_addr[INDEX_WIDTH-1:0]].state == CSMD
    ) |-> (arbiter_busy == 1);
  endproperty

  assert property (p_arbiter_busy_atomic) else
  $error("ERROR: arbiter_busy never asserted in atomic states!");

endmodule
