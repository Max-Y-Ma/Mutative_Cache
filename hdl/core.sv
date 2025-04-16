module core
(
  input  logic        clk,
  input  logic        rst

  // Icache Coherence Port

  // Dcache Coherence Port
);

/* Cache Signals */
localparam ICACHE_WAYS = 2;
localparam ICACHE_SETS = 16;

localparam DCACHE_WAYS = 2;
localparam DCACHE_SETS = 16;

logic   [31:0]  icache_addr;
logic           icache_read;
logic           icache_write;
logic  [255:0]  icache_rdata;
logic  [255:0]  icache_wdata;
logic           icache_resp;

logic   [31:0]  dcache_addr;
logic           dcache_read;
logic           dcache_write;
logic  [255:0]  dcache_rdata;
logic  [255:0]  dcache_wdata;
logic           dcache_resp;

logic   [31:0]  imem_addr;
logic   [3:0]   imem_rmask;
logic   [31:0]  imem_rdata;
logic           imem_resp;

logic   [31:0]  dmem_addr;
logic   [3:0]   dmem_rmask;
logic   [3:0]   dmem_wmask;
logic   [31:0]  dmem_rdata;
logic   [31:0]  dmem_wdata;
logic           dmem_resp;

logic           instr_ready;

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

  .dfp_addr(icache_addr),
  .dfp_read(icache_read),
  .dfp_write(icache_write),
  .dfp_rdata(icache_rdata),
  .dfp_wdata(icache_wdata),
  .dfp_resp(icache_resp)
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

  .dfp_addr(dcache_addr),
  .dfp_read(dcache_read),
  .dfp_write(dcache_write),
  .dfp_rdata(dcache_rdata),
  .dfp_wdata(dcache_wdata),
  .dfp_resp(dcache_resp)
);

endmodule : core
