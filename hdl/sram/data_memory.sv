module data_memory # (
  parameter  NUM_WORDS      = 2048,
  localparam ADDR_WIDTH     = $clog2(NUM_WORDS),
  parameter  WORDSIZE       = 32,
  localparam WORDSIZE_BYTES = WORDSIZE / 8,
  localparam WORDSIZE_WIDTH = $clog2(WORDSIZE_BYTES)
) (
  input  logic                      clk,
  input  logic                      rst,
  input  logic [WORDSIZE-1:0]       dmem_addr,
  input  logic [WORDSIZE_BYTES-1:0] dmem_rmask,
  input  logic [WORDSIZE_BYTES-1:0] dmem_wmask,
  output logic [WORDSIZE-1:0]       dmem_rdata,
  input  logic [WORDSIZE-1:0]       dmem_wdata,
  output logic                      dmem_resp
);

// Active low global write enable signal
logic gwenb_comb;
assign gwenb_comb = ~(|dmem_wmask);

logic gwenb_ff;
always_ff @(posedge clk, posedge rst) begin
  if (rst) gwenb_ff <= '0;
  else     gwenb_ff <= gwenb_comb;
end

logic gwenb;
assign gwenb = gwenb_comb & gwenb_ff;

// Active low chip enable signal
logic cenb_comb;
assign cenb_comb = ~(|dmem_rmask) & gwenb_comb;

logic cenb_ff;
always_ff @(posedge clk, posedge rst) begin
  if (rst) cenb_ff <= '0;
  else     cenb_ff <= cenb_comb;
end

logic cenb;
assign cenb = cenb_comb & cenb_ff;

// Data memory access latency is 1 cycle
always_ff @(posedge clk, posedge rst) begin
  if (rst)             dmem_resp <= 1'b0;
  else if (~cenb_comb) dmem_resp <= 1'b1;
  else                 dmem_resp <= 1'b0;
end

logic [3:0] dmem_wmaskb;
assign dmem_wmaskb = ~dmem_wmask;

logic [ADDR_WIDTH-1:0] dmem_addr_aligned;
assign dmem_addr_aligned = dmem_addr[ADDR_WIDTH+WORDSIZE_WIDTH-1:WORDSIZE_WIDTH];

// 8KB ARM Data SRAM: 2048 x 32
data_sram data_sram0 (
  .CLK(clk),
  .CEN(cenb),
  .WEN(dmem_wmaskb),
  .A(dmem_addr_aligned),
  .D(dmem_wdata),
  .Q(dmem_rdata),
  .EMA(3'b000),
  .GWEN(gwenb),
  .RETN(1'b1)
);

endmodule : data_memory