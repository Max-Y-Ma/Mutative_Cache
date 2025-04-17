module chip
import cache_types::*;
#(
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

// Chip Signals
req_bus_t  req_bus_msg;
req_bus_t  req_bus_tx [NUM_CACHE];
logic       [NUM_CACHE-1:0]              req_bus_gnt;
logic       [NUM_CACHE-1:0]              req_bus_req;
logic       [NUM_CACHE:0]                req_bus_busy;
resp_bus_t resp_bus_tx [NUM_CACHE];
resp_bus_t resp_bus_msg;
logic       [NUM_CACHE-1:0]              resp_bus_gnt;
logic       [NUM_CACHE-1:0]              resp_bus_req;
logic       [NUM_CACHE:0]                resp_bus_busy;

logic invalidate;
logic [XLEN-1:0] invalidate_addr;

logic   [31:0]  l2cache_addr;
logic           l2cache_read;
logic           l2cache_write;
logic  [255:0]  l2cache_rdata;
logic  [255:0]  l2cache_wdata;
logic           l2cache_resp;

// Instantiate Cores
// Instantiate Coherence Interconnect Modules
//   for (genvar i = 0; i < NUM_CACHE; i++) begin : gen_core_inst
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

// Instantiate Cacheline Buffer
cache_line cache_line0(
  .clk(clk),
  .rst(rst),
  
  .bmem_addr(bmem_addr),
  .bmem_read(bmem_read),
  .bmem_write(bmem_write),
  .bmem_wdata(bmem_wdata),
  .bmem_ready(bmem_ready),
  .bmem_raddr(bmem_raddr),
  .bmem_rdata(bmem_rdata),
  .bmem_rvalid(bmem_rvalid),

  .icache_addr(icache_addr),
  .icache_read(icache_read),
  .icache_write(icache_write),
  .icache_rdata(icache_rdata),
  .icache_wdata(icache_wdata),
  .icache_resp(icache_resp),

  .dcache_addr(dcache_addr),
  .dcache_read(dcache_read),
  .dcache_write(dcache_write),
  .dcache_rdata(dcache_rdata),
  .dcache_wdata(dcache_wdata),
  .dcache_resp(dcache_resp)
);

// Instantiate L2 Unified Cache
l2cache #(
  .WAYS(L2CACHE_WAYS),
  .SETS(L2CACHE_SETS)
) l2cache0 (
  .clk(),
  .rst(),
  .req_bus_msg(),
  .resp_bus_msg(),
  .resp_bus_tx(),
  .resp_bus_gnt(),
  .resp_bus_req(),
  .resp_bus_busy(),
  .invalidate(),
  .invalidate_addr(),
  .dfp_addr(),
  .dfp_read(),
  .dfp_write(),
  .dfp_rdata(),
  .dfp_wdata(),
  .dfp_resp()
);

endmodule
