module l2cache_coherence
import cache_types::*;
#(
  parameter integer ID   = 0,
  parameter integer WAYS = 4,
  parameter integer SETS = 16
) (
  input   logic           clk,
  input   logic           rst,

  // Cache Request and Response Signals
  output logic            ufp_resp,
  input  logic [255:0]    ufp_rdata,

  input  logic            dfp_resp,
  output logic            resp_dfp_write,
  output logic [255:0]    resp_dfp_wdata,

  input  logic [WAYS-1:0] cache_hit_vector,
  input  logic [WAYS-1:0] resp_bus_hit_vector,
  input  logic [WAYS-1:0] evict_candidate,

  // Coherence Side Signals
  input  req_msg_t        req_bus_msg,   // Active Request Bus Message

  input  resp_msg_t       resp_bus_msg,  // Active Response Bus Message
  output resp_msg_t       resp_bus_tx,   // Arbiter Message
  input  logic            resp_bus_gnt,  // Arbiter Grant
  output logic            resp_bus_req,  // Arbiter Request
  output logic            resp_bus_busy, // Arbiter Stall

  // Inclusive Policy Signals
  input  logic            invalidate,
  output logic            invalidate_req,
  input  logic            invalidate_resp,
  input  logic [XLEN-1:0] invalidate_addr,
  output logic            invalidate_done
);

  parameter integer INDEX_WIDTH     = $clog2(SETS);
  parameter integer CACHELINE_BYTES = 32;
  parameter integer CACHELINE_BITS  = $clog2(CACHELINE_BYTES);
  parameter integer TAG_BITS        = 32 - INDEX_WIDTH - CACHELINE_BITS;

  llc_memory_state_t [SETS-1:0] state      [WAYS];
  llc_memory_state_t [SETS-1:0] state_next [WAYS];

  // Coherence Logic Signals
  logic                   resp_bus_req_next;
  logic                   resp_bus_req_reg;
  resp_msg_t              resp_bus_tx_next;
  resp_msg_t              resp_bus_tx_reg;

  logic [INDEX_WIDTH-1:0] req_bus_index;
  logic [INDEX_WIDTH-1:0] resp_bus_index;
  logic [INDEX_WIDTH-1:0] invalidate_index;

  logic                   invalidate_req_next;
  logic                   invalidate_req_reg;
  logic                   invalidate_done_next;
  logic                   invalidate_done_reg;

  // Bus Update Logic
  assign req_bus_index    = req_bus_msg.addr[INDEX_WIDTH-1:0];
  assign resp_bus_index   = resp_bus_msg.addr[INDEX_WIDTH-1:0];
  assign invalidate_index = invalidate_addr[INDEX_WIDTH-1:0];

  always_comb begin
    state_next = state;

    for (int i = 0; i < WAYS; i++) begin
      if (req_bus_msg.valid) begin
        unique case (state[i][req_bus_index])
          MI : begin
            // GetS -> EORMRD
            if (req_bus_msg.bus_tx == GETS && cache_hit_vector[i]) begin
              state_next[i][req_bus_index] = MEORMRD;
            end
            // GetM -> EORMRD
            else if (req_bus_msg.bus_tx == GETM && cache_hit_vector[i]) begin
              state_next[i][req_bus_index] = MEORMRD;
            end
            // PutM -> ID
            else if (req_bus_msg.bus_tx == PUTM && cache_hit_vector[i]) begin
              state_next[i][req_bus_index] = MID;
            end
          end
          MS : begin
            // GetS -> SRD
            if (req_bus_msg.bus_tx == GETS && cache_hit_vector[i]) begin
              state_next[i][req_bus_index] = MSRD;
            end
            // GetM -> EORMRD
            else if (req_bus_msg.bus_tx == GETM && cache_hit_vector[i]) begin
              state_next[i][req_bus_index] = MEORMRD;
            end
            // PutM -> SD
            else if (req_bus_msg.bus_tx == PUTM && cache_hit_vector[i]) begin
              state_next[i][req_bus_index] = MSD;
            end
          end
          MEORM : begin
            // GetS -> SD
            if (req_bus_msg.bus_tx == GETS && cache_hit_vector[i]) begin
              state_next[i][req_bus_index] = MSD;
            end
            // GetM -> EORM
            else if (req_bus_msg.bus_tx == GETM && cache_hit_vector[i]) begin
              state_next[i][req_bus_index] = MEORM;
            end
            // PutM -> EORMD
            else if (req_bus_msg.bus_tx == PUTM && cache_hit_vector[i]) begin
              state_next[i][req_bus_index] = MEORMD;
            end
          end
          // Atomic Transactions -> ID, SD, EORMD
          default: begin
          end
        endcase
      end
      else if (resp_bus_msg.valid) begin
        unique case (state[i][resp_bus_index])
          MID : begin
            // DATA -> I
            if (resp_bus_msg.memory_flag && resp_bus_msg.mmsg == DATA && resp_bus_hit_vector[i]) begin
              state_next[i][resp_bus_index] = MI;
            end
            // NODATA -> I
            else if (resp_bus_msg.memory_flag && resp_bus_msg.mmsg == NODATA && resp_bus_hit_vector[i]) begin
              state_next[i][resp_bus_index] = MI;
            end
            // NODATAE -> I
            else if (resp_bus_msg.memory_flag && resp_bus_msg.mmsg == NODATAE && resp_bus_hit_vector[i]) begin
              state_next[i][resp_bus_index] = MI;
            end
          end
          MSD : begin
            // DATA -> S
            if (resp_bus_msg.memory_flag && resp_bus_msg.mmsg == DATA && resp_bus_hit_vector[i]) begin
              state_next[i][resp_bus_index] = MS;
            end
            // NODATA -> S
            else if (resp_bus_msg.memory_flag && resp_bus_msg.mmsg == NODATA && resp_bus_hit_vector[i]) begin
              state_next[i][resp_bus_index] = MS;
            end
            // NODATAE -> S
            else if (resp_bus_msg.memory_flag && resp_bus_msg.mmsg == NODATAE && resp_bus_hit_vector[i]) begin
              state_next[i][resp_bus_index] = MS;
            end
          end
          MSRD: begin
            if (resp_bus_msg.source == ID && resp_bus_msg.way == i) begin
              state_next[i][resp_bus_index] = MS;
            end
          end
          MEORMRD: begin
            if (resp_bus_msg.source == ID && resp_bus_msg.way == i) begin
              state_next[i][resp_bus_index] = MEORM;
            end
          end
          MEORMD : begin
            // DATA -> I
            if (resp_bus_msg.memory_flag && resp_bus_msg.mmsg == DATA && resp_bus_hit_vector[i]) begin
              state_next[i][resp_bus_index] = MI;
            end
            // NODATA -> EORM
            else if (resp_bus_msg.memory_flag && resp_bus_msg.mmsg == NODATA && resp_bus_hit_vector[i]) begin
              state_next[i][resp_bus_index] = MEORM;
            end
            // NODATAE -> I
            else if (resp_bus_msg.memory_flag && resp_bus_msg.mmsg == NODATAE && resp_bus_hit_vector[i]) begin
              state_next[i][resp_bus_index] = MI;
            end
          end
          // Ignore Transactions -> I, S, EORM
          default: begin
          end
        endcase
      end
    end
  end

  // Bus Request Update Logic
  always_comb begin
    resp_dfp_write    = '0;
    resp_dfp_wdata    = 'x;
    resp_bus_req_next = resp_bus_req_reg;
    resp_bus_tx_next  = resp_bus_tx_reg;
    ufp_resp          = resp_bus_gnt;

    for (int i = 0; i < WAYS; i++) begin
      if (req_bus_msg.valid) begin
        unique case (state[i][req_bus_index])
          MI : begin
            // GetS -> Send Data to Requestor (Exclusive), resp_bus_req_next = 1
            if (req_bus_msg.bus_tx == GETS && cache_hit_vector[i]) begin
              resp_bus_req_next = '1;
              resp_bus_tx_next = '{
                valid: '1,
                source: ID,
                way: i,
                destination: req_bus_msg.source,
                memory_flag: '0,
                addr: req_bus_msg.addr,
                data: ufp_rdata,
                mmsg: EXCLUSIVE
              };
            end
            // GetS -> Send Data to Requestor
            else if (req_bus_msg.bus_tx == GETM && cache_hit_vector[i]) begin
              resp_bus_req_next = '1;
              resp_bus_tx_next = '{
                valid: '1,
                source: ID,
                way: i,
                destination: req_bus_msg.source,
                memory_flag: '0,
                addr: req_bus_msg.addr,
                data: ufp_rdata,
                mmsg: DATA
              };
            end
          end
          MS : begin
            // GetS -> Send Data to Requestor (Exclusive), resp_bus_req_next = 1
            if (req_bus_msg.bus_tx == GETS && cache_hit_vector[i]) begin
              resp_bus_req_next = '1;
              resp_bus_tx_next = '{
                valid: '1,
                source: ID,
                way: i,
                destination: req_bus_msg.source,
                memory_flag: '0,
                addr: req_bus_msg.addr,
                data: ufp_rdata,
                mmsg: DATA
              };
            end
            // GetS -> Send Data to Requestor
            else if (req_bus_msg.bus_tx == GETM && cache_hit_vector[i]) begin
              resp_bus_req_next = '1;
              resp_bus_tx_next = '{
                valid: '1,
                source: ID,
                way: i,
                destination: req_bus_msg.source,
                memory_flag: '0,
                addr: req_bus_msg.addr,
                data: ufp_rdata,
                mmsg: DATA
              };
            end
          end
          // Ignore Transactions -> EORM, ID, SD, EORMD
          default: begin
          end
        endcase
      end
      else if (resp_bus_msg.valid) begin
        unique case (state[i][resp_bus_index])
          MSRD : begin
            if (resp_bus_msg.source == ID && resp_bus_msg.way == i) begin
              resp_bus_req_next = '0;
            end
          end
          MEORMRD : begin
            if (resp_bus_msg.source == ID && resp_bus_msg.way == i) begin
              resp_bus_req_next = '0;
            end
          end
          MID : begin
            // DATA -> Write Data to Memory
            if (resp_bus_msg.memory_flag && resp_bus_msg.mmsg == DATA && resp_bus_hit_vector[i]) begin
              resp_dfp_write = '1;
              resp_dfp_wdata = resp_bus_msg.data;
            end
          end
          MSD : begin
            // DATA -> Write Data to Memory
            if (resp_bus_msg.memory_flag && resp_bus_msg.mmsg == DATA && resp_bus_hit_vector[i]) begin
              resp_dfp_write = '1;
              resp_dfp_wdata = resp_bus_msg.data;
            end
          end
          MEORMD : begin
            // DATA -> Write Data to Memory
            if (resp_bus_msg.memory_flag && resp_bus_msg.mmsg == DATA && resp_bus_hit_vector[i]) begin
              resp_dfp_write = '1;
              resp_dfp_wdata = resp_bus_msg.data;
            end
          end
          // Ignore Transactions -> I, S, EORM
          default: begin
          end
        endcase
      end
    end
  end

  assign resp_bus_req  = resp_bus_req_next;
  assign resp_bus_tx   = resp_bus_tx_next;

  // Invalidate Logic
  always_comb begin
    invalidate_req_next  = invalidate_req_reg;
    invalidate_done_next = invalidate_done_reg;

    if (invalidate) begin
      for (int i = 0; i < WAYS; i++) begin
        unique case (state[i][invalidate_index])
          MI: begin
            if (evict_candidate[i]) begin
              invalidate_req_next = '0;
              invalidate_done_next = '1;
            end
          end
          MS: begin
            if (evict_candidate[i]) begin
              invalidate_req_next = '1;
              invalidate_done_next = invalidate_resp;
            end
          end
          MEORM: begin
            if (evict_candidate[i]) begin
              invalidate_req_next = '1;
              invalidate_done_next = invalidate_resp && dfp_resp;
            end
          end
        endcase
      end
    end
    else begin
      invalidate_req_next = '0;
      invalidate_done_next = '0;
    end
  end

  assign invalidate_req  = invalidate_req_next;
  assign invalidate_done = invalidate_done_next;

  // State Logic
  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 0; i < WAYS; i++) begin
        state[i] <= '{default: MI};
      end

      resp_bus_req_reg    <= '0;
      resp_bus_tx_reg     <= '0;
      invalidate_done_reg <= '0;
      invalidate_req_reg  <= '0;
    end
    else begin
      for (int i = 0; i < WAYS; i++) begin
        state[i] <= state_next[i];
      end

      resp_bus_req_reg    <= resp_bus_req_next;
      resp_bus_tx_reg     <= resp_bus_tx_next;
      invalidate_done_reg <= invalidate_done_next;
      invalidate_req_reg  <= invalidate_req_next;
    end
  end

endmodule
