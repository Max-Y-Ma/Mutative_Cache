module rvfi_hookups (

);

/* Model the same RVFI hookups for gate-level simulation
// Latch to Pipeline Registers
always_ff @(posedge clk, posedge rst) begin
  if (rst) begin
    // Reset Pipeline Registers
    if_stage_reg.pc       <= '0;
    if_stage_reg.pc_next  <= '0;
    if_stage_reg.rvfi     <= '0;
    if_stage_reg.int_flag <= '0;
  end else if (!if_stall) begin
    // Latch Program Counters
    if_stage_reg.pc      <= imem_addr;
    if_stage_reg.pc_next <= imem_addr + 'd4;

    // Interrupt Flag Signal
    if_stage_reg.int_flag <= int_instr;

    // Latch RVFI Signals
    if_stage_reg.rvfi          <= '0;
    if_stage_reg.rvfi.valid    <= 1'b1 && !int_instr;
    if_stage_reg.rvfi.pc_rdata <= imem_addr;
    if_stage_reg.rvfi.pc_wdata <= imem_addr + 'd4;
  end
end

// Latch to Pipeline Registers
always_ff @(posedge clk, posedge rst) begin
  // During a load hazard or flush, pass a bubble on the next available cycle
  if (rst) begin
    id_stage_reg.pc         <= '0;
    id_stage_reg.pc_next    <= '0;
    id_stage_reg.rs1_addr   <= '0;
    id_stage_reg.rs2_addr   <= '0;
    id_stage_reg.rd_addr    <= '0;
    id_stage_reg.imm        <= '0;
    id_stage_reg.rs1_rdata  <= '0;
    id_stage_reg.rs2_rdata  <= '0;
    id_stage_reg.ex_ctrl    <= '0;
    id_stage_reg.mem_ctrl   <= '0;
    id_stage_reg.wb_ctrl    <= '0;
    id_stage_reg.int_flag   <= '0;
    id_stage_reg.rvfi       <= '0;
  end 
  else if (((load_hazard || id_flush) & !ex_stall)) begin
    id_stage_reg.pc         <= '0;
    id_stage_reg.pc_next    <= '0;
    id_stage_reg.rs1_addr   <= '0;
    id_stage_reg.rs2_addr   <= '0;
    id_stage_reg.rd_addr    <= '0;
    id_stage_reg.imm        <= '0;
    id_stage_reg.rs1_rdata  <= '0;
    id_stage_reg.rs2_rdata  <= '0;
    id_stage_reg.ex_ctrl    <= '0;
    id_stage_reg.mem_ctrl   <= '0;
    id_stage_reg.wb_ctrl    <= '0;
    id_stage_reg.int_flag   <= '0;
    id_stage_reg.rvfi       <= '0;
  end
  else if (!id_stall) begin
    // Latch Program Counters
    id_stage_reg.pc      <= if_stage_reg.pc;
    id_stage_reg.pc_next <= o_compressed ?
                            if_stage_reg.pc_next - 'd2 :
                            if_stage_reg.pc_next;

    // Latch Immediate Value
    id_stage_reg.imm <= imm;

    // Latch Register File Data
    id_stage_reg.rs1_addr  <= rs1_addr;
    id_stage_reg.rs2_addr  <= rs2_addr;
    id_stage_reg.rd_addr   <= rd_addr;
    id_stage_reg.rs1_rdata <= rs1_rdata;
    id_stage_reg.rs2_rdata <= rs2_rdata;

    // Latch Control Signals
    id_stage_reg.ex_ctrl  <= ex_ctrl;
    id_stage_reg.mem_ctrl <= mem_ctrl;
    id_stage_reg.wb_ctrl  <= wb_ctrl;

    //Interrupt Flag Signal
    id_stage_reg.int_flag <= if_stage_reg.int_flag;

    // Latch RVFI Signals
    id_stage_reg.rvfi           <= '0;
    id_stage_reg.rvfi.valid     <= if_stage_reg.rvfi.valid;
    id_stage_reg.rvfi.order     <= order;
    id_stage_reg.rvfi.inst      <= inst_raw;
    id_stage_reg.rvfi.rs1_addr  <= rs1_addr;
    id_stage_reg.rvfi.rs2_addr  <= rs2_addr;
    id_stage_reg.rvfi.rs1_rdata <= rs1_rdata;
    id_stage_reg.rvfi.rs2_rdata <= rs2_rdata;
    id_stage_reg.rvfi.rd_addr   <= rd_addr;
    id_stage_reg.rvfi.pc_rdata  <= if_stage_reg.rvfi.pc_rdata;
    id_stage_reg.rvfi.pc_wdata  <= o_compressed ? 
                                   if_stage_reg.rvfi.pc_wdata - 'd2 : 
                                   if_stage_reg.rvfi.pc_wdata;
  end

// Latch to Pipeline Registers
always_ff @(posedge clk, posedge rst) begin
  if (rst) begin
    // Reset Pipeline Registers
    ex_stage_reg.func_out  <= '0;
    ex_stage_reg.rs2_rdata <= '0;
    ex_stage_reg.rd_addr   <= '0;
    ex_stage_reg.mem_ctrl  <= '0;
    ex_stage_reg.wb_ctrl   <= '0;
    ex_stage_reg.rvfi      <= '0;
  end else if (!ex_stall) begin
    // Latch Data Signals
    ex_stage_reg.func_out  <= func_out__;
    ex_stage_reg.rs2_rdata <= fwd_src_b_data;
    ex_stage_reg.rd_addr   <= id_stage_reg.rd_addr;

    // Latch Control Signals
    ex_stage_reg.mem_ctrl <= id_stage_reg.mem_ctrl;
    ex_stage_reg.wb_ctrl  <= id_stage_reg.wb_ctrl;

    // Latch RVFI Signals
    ex_stage_reg.rvfi           <= '0;
    ex_stage_reg.rvfi.valid     <= id_stage_reg.rvfi.valid;
    ex_stage_reg.rvfi.order     <= id_stage_reg.rvfi.order;
    ex_stage_reg.rvfi.inst      <= id_stage_reg.rvfi.inst;
    ex_stage_reg.rvfi.rs1_addr  <= id_stage_reg.rvfi.rs1_addr;
    ex_stage_reg.rvfi.rs2_addr  <= id_stage_reg.rvfi.rs2_addr;
    ex_stage_reg.rvfi.rs1_rdata <= fwd_src_a_data;
    ex_stage_reg.rvfi.rs2_rdata <= fwd_src_b_data;
    ex_stage_reg.rvfi.rd_addr   <= id_stage_reg.rvfi.rd_addr;
    ex_stage_reg.rvfi.pc_rdata  <= id_stage_reg.rvfi.pc_rdata;
    ex_stage_reg.rvfi.pc_wdata  <= branch_taken ? o_pc_offset : id_stage_reg.rvfi.pc_wdata;
  end
end

// Latch to Pipeline Registers
always_ff @(posedge clk, posedge rst) begin
  if (rst) begin
    // Reset Pipeline Registers
    mem_stage_reg.rd_addr    <= '0;
    mem_stage_reg.func_out   <= '0;
    mem_stage_reg.mem_ctrl   <= '0;
    mem_stage_reg.wb_ctrl    <= '0;
    mem_stage_reg.rvfi       <= '0;
  end else if (!mem_stall) begin
    // Latch Data Signals
    mem_stage_reg.rd_addr  <= ex_stage_reg.rd_addr;
    mem_stage_reg.func_out <= ex_stage_reg.func_out;
    
    // Latch Control Signals
    mem_stage_reg.mem_ctrl <= ex_stage_reg.mem_ctrl;
    mem_stage_reg.wb_ctrl  <= ex_stage_reg.wb_ctrl;

    // Latch RVFI Signals
    mem_stage_reg.rvfi           <= '0;
    mem_stage_reg.rvfi.valid     <= ex_stage_reg.rvfi.valid;
    mem_stage_reg.rvfi.order     <= ex_stage_reg.rvfi.order;
    mem_stage_reg.rvfi.inst      <= ex_stage_reg.rvfi.inst;
    mem_stage_reg.rvfi.rs1_addr  <= ex_stage_reg.rvfi.rs1_addr;
    mem_stage_reg.rvfi.rs2_addr  <= ex_stage_reg.rvfi.rs2_addr;
    mem_stage_reg.rvfi.rs1_rdata <= ex_stage_reg.rvfi.rs1_rdata;
    mem_stage_reg.rvfi.rs2_rdata <= ex_stage_reg.rvfi.rs2_rdata;
    mem_stage_reg.rvfi.rd_addr   <= ex_stage_reg.rvfi.rd_addr;
    mem_stage_reg.rvfi.pc_rdata  <= ex_stage_reg.rvfi.pc_rdata;
    mem_stage_reg.rvfi.pc_wdata  <= ex_stage_reg.rvfi.pc_wdata;
    mem_stage_reg.rvfi.mem_addr  <= dmem_addr;
    mem_stage_reg.rvfi.mem_rmask <= (!mem_stall) ? dmem_rmask : rvfi_mem_rmask;
    mem_stage_reg.rvfi.mem_wmask <= (!mem_stall) ? dmem_wmask : rvfi_mem_wmask;
    mem_stage_reg.rvfi.mem_wdata <= dmem_wdata;
  end
end

// Latch to Pipeline Registers
always_ff @(posedge clk, posedge rst) begin
  if (rst) begin
    // Reset Pipeline Registers
    wb_stage_reg.rvfi <= '0;
  end else if (!wb_stall) begin
    // Latch Data Signals
    wb_stage_reg.rvfi.valid     <= mem_stage_reg.rvfi.valid;
    wb_stage_reg.rvfi.order     <= mem_stage_reg.rvfi.order;
    wb_stage_reg.rvfi.inst      <= mem_stage_reg.rvfi.inst;
    wb_stage_reg.rvfi.rs1_addr  <= mem_stage_reg.rvfi.rs1_addr;
    wb_stage_reg.rvfi.rs2_addr  <= mem_stage_reg.rvfi.rs2_addr;
    wb_stage_reg.rvfi.rs1_rdata <= mem_stage_reg.rvfi.rs1_rdata;
    wb_stage_reg.rvfi.rs2_rdata <= mem_stage_reg.rvfi.rs2_rdata;
    wb_stage_reg.rvfi.rd_addr   <= mem_stage_reg.rvfi.rd_addr;
    wb_stage_reg.rvfi.rd_wdata  <= o_write_data;
    wb_stage_reg.rvfi.pc_rdata  <= mem_stage_reg.rvfi.pc_rdata;
    wb_stage_reg.rvfi.pc_wdata  <= mem_stage_reg.rvfi.pc_wdata;
    wb_stage_reg.rvfi.mem_addr  <= mem_stage_reg.rvfi.mem_addr;
    wb_stage_reg.rvfi.mem_rmask <= mem_stage_reg.rvfi.mem_rmask;
    wb_stage_reg.rvfi.mem_wmask <= mem_stage_reg.rvfi.mem_wmask;
    wb_stage_reg.rvfi.mem_rdata <= mem_rdata_raw;
    wb_stage_reg.rvfi.mem_wdata <= mem_stage_reg.rvfi.mem_wdata;
  end
end

*/

endmodule : rvfi_hookups