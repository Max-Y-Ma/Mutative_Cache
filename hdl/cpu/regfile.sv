// 2 Asynchronous Read Port, 1 Synchronous Write Port Register File
module regfile #(
  parameter NUM_REGS = 32
) (
  input  logic        clk, rst,
  input  logic        regf_we,
  input  logic [31:0] rd_wdata,
  input  logic [4:0]  rd_addr, rs1_addr, rs2_addr,
  output logic [31:0] rs1_rdata, rs2_rdata
);

// Register File Data
logic [31:0] data [NUM_REGS];

// 1 Synchronous Write Port
always_ff @(posedge clk) begin
  if (rst) begin
    for (int i = 0; i < 32; i++) begin
      data[i] <= '0;
    end
  end else if (regf_we && (rd_addr != 5'd0)) begin
    data[rd_addr] <= rd_wdata;
  end
end

// 2 Asynchronous Read Port
always_comb begin
  if (rst) begin
    rs1_rdata = 'x;
    rs2_rdata = 'x;
  end else begin
    if (rs1_addr == 5'd0) begin
      rs1_rdata = '0;
    end else if (rs1_addr == rd_addr) begin
      rs1_rdata = rd_wdata;
    end else begin
      rs1_rdata = data[rs1_addr];
    end

    if (rs2_addr == 5'd0) begin
      rs2_rdata = '0;
    end else if (rs2_addr == rd_addr) begin
      rs2_rdata = rd_wdata;
    end else begin
      rs2_rdata = data[rs2_addr];
    end
  end
end

endmodule : regfile
