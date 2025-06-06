module cpu
import types::*;
(
  input   logic           clk,
  input   logic           rst
);

  // Core to Cache
  logic                                   cpu_ready [NUM_CPUS];
  logic                                   cpu_resp  [NUM_CPUS];
  logic                                   cpu_req   [NUM_CPUS];
  logic                                   cpu_we    [NUM_CPUS];
  logic       [XLEN-1:0]                  cpu_addr  [NUM_CPUS];
  logic       [CACHELINE_SIZE-1:0]        cpu_wdata [NUM_CPUS];
  logic       [CACHELINE_SIZE-1:0]        cpu_rdata [NUM_CPUS];

  // Arbiter
  logic       [NUM_CPUS-1:0]              done;
  logic       [NUM_CPUS-1:0]              arbiter_gnt;
  logic       [NUM_CPUS-1:0]              arbiter_req;
  logic       [NUM_CPUS:0]                arbiter_busy;

  // Snoop Bus
  logic       [XLEN-1:0]                  bus_addr [NUM_CPUS];
  bus_tx_t                                bus_tx   [NUM_CPUS];
  bus_msg_t                               bus_msg;

  // Xbar
  xbar_msg_t                              xbar_in  [NUM_CPUS+1];
  xbar_msg_t                              xbar_out [NUM_CPUS+1][NUM_CPUS];

  for (genvar i = 0; i < NUM_CPUS; i++) begin : gen_core_inst
    core #(
      .ID(i)
    ) core_inst (
      .clk(clk),
      .rst(rst),

      .cpu_ready(cpu_ready[i]),
      .cpu_resp(cpu_resp[i]),
      .cpu_req(cpu_req[i]),
      .cpu_we(cpu_we[i]),
      .cpu_addr(cpu_addr[i]),
      .cpu_wdata(cpu_wdata[i]),
      .cpu_rdata(cpu_rdata[i]),
      .done(done[i])
    );

    cache #(
      .ID(i)
    ) cache_inst (
      .clk(clk),
      .rst(rst),

      .cpu_ready(cpu_ready[i]),
      .cpu_resp(cpu_resp[i]),
      .cpu_req(cpu_req[i]),
      .cpu_we(cpu_we[i]),
      .cpu_addr(cpu_addr[i]),
      .cpu_wdata(cpu_wdata[i]),
      .cpu_rdata(cpu_rdata[i]),

      .bus_addr(bus_addr[i]),
      .bus_tx(bus_tx[i]),
      .bus_msg(bus_msg),

      .arbiter_req(arbiter_req[i]),
      .arbiter_gnt(arbiter_gnt[i]),
      .arbiter_busy(arbiter_busy[i]),

      .xbar_in(xbar_out[i]),
      .xbar_out(xbar_in[i])
    );
  end

  arbiter arbiter_inst (
    .clk(clk),
    .rst(rst),

    .req(arbiter_req),
    .gnt(arbiter_gnt),
    .busy(arbiter_busy)
  );

  snoop_bus snoop_bus_inst (
    .clk(clk),
    .gnt(arbiter_gnt),
    .bus_addr(bus_addr),
    .bus_tx(bus_tx),
    .bus_msg(bus_msg)
  );

  xbar xbar_inst (
    .clk(clk),
    .rst(rst),
    .xbar_in(xbar_in),
    .xbar_out(xbar_out)
  );

  memory memory_inst (
    .clk(clk),
    .rst(rst),

    .xbar_in(xbar_out[NUM_CPUS]),
    .xbar_out(xbar_in[NUM_CPUS]),

    .bus_msg(bus_msg),
    .arbiter_busy(arbiter_busy[NUM_CPUS])
  );

  always_ff @(posedge clk) begin
    if (&done) begin
      $info("Finished Test!");
      $finish;
    end
  end

  // If a cacheline in one core is in Exclusive state, all other cachelines are in invalid states
  for (genvar i = 0; i < NUM_CPUS; i++) begin : gen_exclusive_state_check_out
    for (genvar j = 0; j < NUM_SETS; j++) begin : gen_exclusive_state_check_mid
      for (genvar k = 0; k < NUM_CPUS - 1; k++) begin : gen_exclusive_state_check_in
        if (k >= i) begin : gen_exclusive_state_if
          property p_cache_exclusive_state;
            @(posedge clk) disable iff (rst)
            (top_tb.dut.gen_core_inst[i].cache_inst.cacheline[j].state == CE &&
            (top_tb.dut.gen_core_inst[i].cache_inst.cacheline[j].tag ==
             top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].tag)
            )
            |-> (
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CI ||
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CISAD ||
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CISD ||
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CIMAD ||
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CIMD ||
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CMIA ||
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CEIA ||
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CIIA
            );
          endproperty

          assert property (p_cache_exclusive_state) else
          $error("Read or write state not followed by IDLE state");
        end
        else begin : gen_exclusive_state_else
          property p_cache_exclusive_state;
            @(posedge clk) disable iff (rst)
            (top_tb.dut.gen_core_inst[i].cache_inst.cacheline[j].state == CE &&
            (top_tb.dut.gen_core_inst[i].cache_inst.cacheline[j].tag ==
             top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].tag)
            )
            |-> (
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CI ||
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CISAD ||
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CISD ||
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CIMAD ||
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CIMD ||
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CMIA ||
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CEIA ||
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CIIA
            );
          endproperty

          assert property (p_cache_exclusive_state) else
          $error("Read or write state not followed by IDLE state");
        end
      end
    end
  end

  // If a cacheline in one core is in Modified state, all other cachelines are in invalid states
  for (genvar i = 0; i < NUM_CPUS; i++) begin : gen_modified_state_check_out
    for (genvar j = 0; j < NUM_SETS; j++) begin : gen_modified_state_check_mid
      for (genvar k = 0; k < NUM_CPUS - 1; k++) begin : gen_modified_state_check_in
        if (k >= i) begin : gen_modified_state_if
          property p_cache_modified_state;
            @(posedge clk) disable iff (rst)
            (top_tb.dut.gen_core_inst[i].cache_inst.cacheline[j].state == CM &&
            (top_tb.dut.gen_core_inst[i].cache_inst.cacheline[j].tag ==
             top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].tag)
            )
            |-> (
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CI ||
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CISAD ||
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CISD ||
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CIMAD ||
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CIMD ||
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CMIA ||
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CEIA ||
              top_tb.dut.gen_core_inst[k+1].cache_inst.cacheline[j].state == CIIA
            );
          endproperty

          assert property (p_cache_modified_state) else
          $error("Read or write state not followed by IDLE state");
        end
        else begin : gen_modified_state_else
          property p_cache_modified_state;
            @(posedge clk) disable iff (rst)
            (top_tb.dut.gen_core_inst[i].cache_inst.cacheline[j].state == CM &&
            (top_tb.dut.gen_core_inst[i].cache_inst.cacheline[j].tag ==
             top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].tag)
            )
            |-> (
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CI ||
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CISAD ||
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CISD ||
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CIMAD ||
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CIMD ||
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CMIA ||
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CEIA ||
              top_tb.dut.gen_core_inst[k].cache_inst.cacheline[j].state == CIIA
            );
          endproperty

          assert property (p_cache_modified_state) else
          $error("Read or write state not followed by IDLE state");
        end
      end
    end
  end

endmodule
