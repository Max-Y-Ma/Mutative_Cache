module chip #(
  // parameters
) (
  // Main Memory Port
  input  logic        clk,
  input  logic        rst,

  output logic [31:0] bmem_addr,
  output logic        bmem_read,
  output logic        bmem_write,
  output logic [63:0] bmem_wdata,
  input  logic        bmem_ready,

  input  logic [31:0] bmem_raddr,
  input  logic [63:0] bmem_rdata,
  input  logic        bmem_rvalid
);

//   // Arbiter
//   logic       [NUM_CPUS-1:0]              done;
//   logic       [NUM_CPUS-1:0]              arbiter_gnt;
//   logic       [NUM_CPUS-1:0]              arbiter_req;
//   logic       [NUM_CPUS:0]                arbiter_busy;

//   // Snoop Bus
//   logic       [XLEN-1:0]                  bus_addr [NUM_CPUS];
//   bus_tx_t                                bus_tx   [NUM_CPUS];
//   bus_msg_t                               bus_msg;

//   // Xbar
//   xbar_msg_t                              xbar_in  [NUM_CPUS+1];
//   xbar_msg_t                              xbar_out [NUM_CPUS+1][NUM_CPUS];

// Instantiate Cores

// Instantiate Coherence Interconnect Modules
//   for (genvar i = 0; i < NUM_CPUS; i++) begin : gen_core_inst
//     core #(
//       .ID(i)
//     ) core_inst (
//       .clk(clk),
//       .rst(rst),

//       .cpu_ready(cpu_ready[i]),
//       .cpu_resp(cpu_resp[i]),
//       .cpu_req(cpu_req[i]),
//       .cpu_we(cpu_we[i]),
//       .cpu_addr(cpu_addr[i]),
//       .cpu_wdata(cpu_wdata[i]),
//       .cpu_rdata(cpu_rdata[i]),
//       .done(done[i])
//     );

//     cache #(
//       .ID(i)
//     ) cache_inst (
//       .clk(clk),
//       .rst(rst),

//       .cpu_ready(cpu_ready[i]),
//       .cpu_resp(cpu_resp[i]),
//       .cpu_req(cpu_req[i]),
//       .cpu_we(cpu_we[i]),
//       .cpu_addr(cpu_addr[i]),
//       .cpu_wdata(cpu_wdata[i]),
//       .cpu_rdata(cpu_rdata[i]),

//       .bus_addr(bus_addr[i]),
//       .bus_tx(bus_tx[i]),
//       .bus_msg(bus_msg),

//       .arbiter_req(arbiter_req[i]),
//       .arbiter_gnt(arbiter_gnt[i]),
//       .arbiter_busy(arbiter_busy[i]),

//       .xbar_in(xbar_out[i]),
//       .xbar_out(xbar_in[i])
//     );
//   end

//   arbiter arbiter_inst (
//     .clk(clk),
//     .rst(rst),

//     .req(arbiter_req),
//     .gnt(arbiter_gnt),
//     .busy(arbiter_busy)
//   );

//   snoop_bus snoop_bus_inst (
//     .clk(clk),
//     .gnt(arbiter_gnt),
//     .bus_addr(bus_addr),
//     .bus_tx(bus_tx),
//     .bus_msg(bus_msg)
//   );

//   xbar xbar_inst (
//     .clk(clk),
//     .rst(rst),
//     .xbar_in(xbar_in),
//     .xbar_out(xbar_out)
//   );

// Instantiate L2 Unified Cache

endmodule
