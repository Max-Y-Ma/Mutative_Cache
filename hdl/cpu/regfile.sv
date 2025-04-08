// 2 Asynchronous Read Port, 1 Synchronous Write Port Register File
module regfile #(
  parameter NUM_REGS = 32
) (
  input  logic        clk, 
  input  logic        rst,
  input  logic        regf_we,
  input  logic [31:0] rd_wdata,
  input  logic [4:0]  rd_addr, 
  input  logic [4:0]  rs1_addr, 
  input  logic [4:0]  rs2_addr,
  output logic [31:0] rs1_rdata,
  output logic [31:0] rs2_rdata,

  // ADP Debug Signals
  input  logic [4:0]  adp_rd_addr,
  input  logic [31:0] adp_wdata,
  input  logic        adp_reg_we,
  output logic [31:0] adp_core_reg [32],

  //Interrupt Signals
  input  logic start_interrupt,
  input  logic int_instr,
  input  logic wb_int_flag,
  input  logic end_interrupt
);

// Register File Data
logic [31:0] data [NUM_REGS];
logic [31:0] interrupt_saved_data [2];

// ADP Debug Signals
assign adp_core_reg = data;

// Int Signals
logic allow_post_int;
logic update_int_registers;

always_comb begin
  //if we are curr_instr_flow and an interrupt needs to write_back
  //don't let any writeback to registers: x1, x2
  if(~int_instr && wb_int_flag && (rd_addr == 5'd1 || rd_addr == 5'd2))
    allow_post_int = 1'b0;
  else 
    allow_post_int = 1'b1;

  //if we are servicing an int, and a instruction in the pipeline updates x1/x2
  //if this instr is from normal execution flow then update the registers
  if(int_instr && ~wb_int_flag && (rd_addr == 5'd1 || rd_addr == 5'd2))
    update_int_registers = 1'b1;
  else
    update_int_registers = 1'b0;
end

// 1 Synchronous Write Port
always_ff @(posedge clk, posedge rst) begin
  if (rst) begin

    for (int i = 0; i < 32; i++) begin
      data[i] <= '0;
    end

  end else begin

    // Suport ADP Debug Register Writes
    if (adp_reg_we && (adp_rd_addr != 5'd0)) begin
      data[adp_rd_addr] <= adp_wdata;
    end
    //don't allow write_back pipeline to overwrite data on the clk cycle 
    //after an end_int is sent
    else if (regf_we && (rd_addr != 5'd0) && (allow_post_int)) begin
      data[rd_addr] <= rd_wdata;
    end 

    //once interrupt is complete, then restore our saved data
    if(end_interrupt) begin
      data[5'd2] <= interrupt_saved_data[5'd1];
      data[5'd1] <= interrupt_saved_data[5'd0];
    end
  end
end


// 1 Synchronous Write Port
always_ff @(posedge clk, posedge rst) begin
  if (rst) begin
    for (int i = 0; i < 2; i++) begin
      interrupt_saved_data[i] <= '0;
    end
  end else if (start_interrupt) begin
    //on the begining of an interrupt, store register 1 and 2
    interrupt_saved_data[5'd1] <= data[5'd2];
    interrupt_saved_data[5'd0] <= data[5'd1];
  end else if (update_int_registers) begin
    interrupt_saved_data[rd_addr - 'd1] <= rd_wdata;
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
    end
    //ensure that wb -> decode forward doesn't forward erroenous x1/x2
    else if ((rs1_addr == rd_addr) && allow_post_int) begin
      rs1_rdata = rd_wdata;
    end 
    else begin
      rs1_rdata = data[rs1_addr];
    end

    if (rs2_addr == 5'd0) begin
      rs2_rdata = '0;
    end 
    else if ((rs2_addr == rd_addr) && allow_post_int) begin
      rs2_rdata = rd_wdata;
    end 
    else begin
      rs2_rdata = data[rs2_addr];
    end
  end
end

endmodule : regfile
