module chip
import cache_types::*;
(
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
req_msg_t                  req_bus_msg;
req_msg_t                  req_bus_tx [NUM_CACHE];
logic      [NUM_CACHE-1:0] req_bus_gnt;
logic      [NUM_CACHE-1:0] req_bus_req;
logic      [NUM_CACHE-1:0] req_bus_busy;

resp_msg_t                 resp_bus_msg;
resp_msg_t                 resp_bus_tx [NUM_CACHE + 1];
logic      [NUM_CACHE:0]   resp_bus_gnt;
logic      [NUM_CACHE:0]   resp_bus_req;
logic      [NUM_CACHE:0]   resp_bus_busy;

logic                      invalidate;
logic      [XLEN-1:0]      invalidate_addr;

logic      [31:0]          l2cache_addr;
logic                      l2cache_read;
logic                      l2cache_write;
logic      [255:0]         l2cache_rdata;
logic      [255:0]         l2cache_wdata;
logic                      l2cache_resp;

// Cores
for (genvar i = 0; i < NUM_CORES; i++) begin : gen_core_inst
  core #(
    .ID(i)
  ) core (
    .clk(clk),
    .rst(rst),
    .req_bus_msg(req_bus_msg),
    .resp_bus_msg(resp_bus_msg),
    .icache_req_bus_tx(req_bus_tx[i]),
    .icache_req_bus_gnt(req_bus_gnt[i]),
    .icache_req_bus_req(req_bus_req[i]),
    .icache_req_bus_busy(req_bus_busy[i]),
    .icache_resp_bus_tx(resp_bus_tx[i]),
    .icache_resp_bus_gnt(resp_bus_gnt[i]),
    .icache_resp_bus_req(resp_bus_req[i]),
    .icache_resp_bus_busy(resp_bus_busy[i]),
    .dcache_req_bus_tx(req_bus_tx[i + 1]),
    .dcache_req_bus_gnt(req_bus_gnt[i + 1]),
    .dcache_req_bus_req(req_bus_req[i + 1]),
    .dcache_req_bus_busy(req_bus_busy[i + 1]),
    .dcache_resp_bus_tx(resp_bus_tx[i + 1]),
    .dcache_resp_bus_gnt(resp_bus_gnt[i + 1]),
    .dcache_resp_bus_req(resp_bus_req[i + 1]),
    .dcache_resp_bus_busy(resp_bus_busy[i + 1]),
    .invalidate(invalidate),
    .invalidate_addr(invalidate_addr)
  );
end

// Request Bus
arbiter # (
  .NUM_NODES(NUM_CACHE)
) req_arbiter0 (
  .clk(clk),
  .rst(rst),
  .req(req_bus_req),
  .gnt(req_bus_gnt),
  .busy(req_bus_busy)
);

snoop_bus # (
  .NUM_NODES(NUM_CACHE),
  .DTYPE(req_msg_t)
) req_snoop_bus0 (
  .clk(clk),
  .gnt(req_bus_gnt),
  .bus_tx(req_bus_tx),
  .bus_msg(req_bus_msg)
);

// Response Bus
arbiter # (
  .NUM_NODES(NUM_CACHE + 1) // + L2 Cache Response
) resp_arbiter0 (
  .clk(clk),
  .rst(rst),
  .req(resp_bus_req),
  .gnt(resp_bus_gnt),
  .busy(resp_bus_busy)
);

snoop_bus # (
  .NUM_NODES(NUM_CACHE + 1), // + L2 Cache Response
  .DTYPE(resp_msg_t)
) resp_snoop_bus0 (
  .clk(clk),
  .gnt(resp_bus_gnt),
  .bus_tx(resp_bus_tx),
  .bus_msg(resp_bus_msg)
);

// Instantiate Cacheline Buffer
line_buffer line_buffer0(
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
  .l2cache_addr(l2cache_addr),
  .l2cache_read(l2cache_read),
  .l2cache_write(l2cache_write),
  .l2cache_rdata(l2cache_rdata),
  .l2cache_wdata(l2cache_wdata),
  .l2cache_resp(l2cache_resp)
);

// Instantiate L2 Unified Cache
l2cache #(
  .ID(NUM_CACHE),
  .WAYS(L2CACHE_WAYS),
  .SETS(L2CACHE_SETS)
) l2cache0 (
  .clk(clk),
  .rst(rst),
  .req_bus_msg(req_bus_msg),
  .resp_bus_msg(resp_bus_msg),
  .resp_bus_tx(resp_bus_tx[NUM_CACHE]),
  .resp_bus_gnt(resp_bus_gnt[NUM_CACHE]),
  .resp_bus_req(resp_bus_req[NUM_CACHE]),
  .resp_bus_busy(resp_bus_busy[NUM_CACHE]),
  .invalidate(invalidate),
  .invalidate_addr(invalidate_addr),
  .dfp_addr(l2cache_addr),
  .dfp_read(l2cache_read),
  .dfp_write(l2cache_write),
  .dfp_rdata(l2cache_rdata),
  .dfp_wdata(l2cache_wdata),
  .dfp_resp(l2cache_resp)
);

endmodule
