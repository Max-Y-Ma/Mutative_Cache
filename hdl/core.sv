module core
import cache_types::*;
# (
  parameter integer ID = 0
) (
  input  logic            clk,
  input  logic            rst,

  // Shared Coherence Port
  input  req_msg_t        req_bus_msg,
  input  resp_msg_t       resp_bus_msg,

  // Icache Coherence Port
  output req_msg_t        icache_req_bus_tx,
  input  logic            icache_req_bus_gnt,
  output logic            icache_req_bus_req,
  output logic            icache_req_bus_busy,
  output resp_msg_t       icache_resp_bus_tx,
  input  logic            icache_resp_bus_gnt,
  output logic            icache_resp_bus_req,
  output logic            icache_resp_bus_busy,

  // Dcache Coherence Port
  output req_msg_t        dcache_req_bus_tx,
  input  logic            dcache_req_bus_gnt,
  output logic            dcache_req_bus_req,
  output logic            dcache_req_bus_busy,
  output resp_msg_t       dcache_resp_bus_tx,
  input  logic            dcache_resp_bus_gnt,
  output logic            dcache_resp_bus_req,
  output logic            dcache_resp_bus_busy,

  // Inclusive Policy Signals
  input  logic            invalidate,
  input  logic [XLEN-1:0] invalidate_addr
);

// Cache Signals
logic   [XLEN-1:0]       imem_addr;
logic   [XLEN_BYTES-1:0] imem_rmask;
logic   [XLEN-1:0]       imem_rdata;
logic                    imem_resp;

logic   [XLEN-1:0]       dmem_addr;
logic   [XLEN_BYTES-1:0] dmem_rmask;
logic   [XLEN_BYTES-1:0] dmem_wmask;
logic   [XLEN-1:0]       dmem_rdata;
logic   [XLEN-1:0]       dmem_wdata;
logic                    dmem_resp;

// RV32IM CPU
cpu cpu0(
  .clk(clk),
  .rst(rst),
  .imem_addr(imem_addr),
  .imem_rmask(imem_rmask),
  .imem_rdata(imem_rdata),
  .imem_resp(imem_resp),
  .dmem_addr(dmem_addr),
  .dmem_rmask(dmem_rmask),
  .dmem_wmask(dmem_wmask),
  .dmem_rdata(dmem_rdata),
  .dmem_wdata(dmem_wdata),
  .dmem_resp(dmem_resp)
);

icache #(
  .WAYS(ICACHE_WAYS),
  .SETS(ICACHE_SETS)
) icache0 (
  .clk(clk),
  .rst(rst),
  .ufp_addr(imem_addr),
  .ufp_rmask(imem_rmask),
  .ufp_rdata(imem_rdata),
  .ufp_resp(imem_resp),
  .req_bus_msg(req_bus_msg),
  .req_bus_tx(icache_req_bus_tx),
  .req_bus_gnt(icache_req_bus_gnt),
  .req_bus_req(icache_req_bus_req),
  .req_bus_busy(icache_req_bus_busy),
  .resp_bus_msg(resp_bus_msg),
  .resp_bus_tx(icache_resp_bus_tx),
  .resp_bus_gnt(icache_resp_bus_gnt),
  .resp_bus_req(icache_resp_bus_req),
  .resp_bus_busy(icache_resp_bus_busy),
  .invalidate(invalidate),
  .invalidate_addr(invalidate_addr),
);

dcache #(
  .WAYS(DCACHE_WAYS),
  .SETS(DCACHE_SETS)
) dcache0 (
  .clk(clk),
  .rst(rst),
  .ufp_addr(dmem_addr),
  .ufp_rmask(dmem_rmask),
  .ufp_wmask(dmem_wmask),
  .ufp_rdata(dmem_rdata),
  .ufp_wdata(dmem_wdata),
  .ufp_resp(dmem_resp),
  .req_bus_msg(req_bus_msg),
  .req_bus_tx(dcache_req_bus_tx),
  .req_bus_gnt(dcache_req_bus_gnt),
  .req_bus_req(dcache_req_bus_req),
  .req_bus_busy(dcache_req_bus_busy),
  .resp_bus_msg(resp_bus_msg),
  .resp_bus_tx(dcache_resp_bus_tx),
  .resp_bus_gnt(dcache_resp_bus_gnt),
  .resp_bus_req(dcache_resp_bus_req),
  .resp_bus_busy(dcache_resp_bus_busy),
  .invalidate(invalidate),
  .invalidate_addr(invalidate_addr),
);

endmodule : core
