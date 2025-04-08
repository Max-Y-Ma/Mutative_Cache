module cpu 
import rv32imc_types::*;
(
  input  logic        clk,
  input  logic        rst,

  // Instruction memory interface
  output logic [31:0] imem_addr,
  output logic [3:0]  imem_rmask,
  input  logic [31:0] imem_rdata,
  input  logic        imem_resp,

  // Data memory interface
  output logic [31:0] dmem_addr,
  output logic [3:0]  dmem_rmask,
  output logic [3:0]  dmem_wmask,
  input  logic [31:0] dmem_rdata,
  output logic [31:0] dmem_wdata,
  input  logic        dmem_resp,

  //Interupt start/stop signals
  input  logic        signal_interrupt,
  input  logic [31:0] interrupt_PC,
  output logic        interrupt_serviced,
  output logic        int_accepted,

  // ADP debug signal interface
  output logic [31:0] adp_core_reg [32],
  output logic [31:0] adp_core_pc,
  output logic [31:0] adp_core_ir,
  input  logic [4:0]  adp_rd_addr,
  input  logic [31:0] adp_wdata,
  input  logic        adp_reg_we,
  input  logic        adp_pc_we,
  input  logic        adp_ir_we,
  output logic        adp_imem_stall,
  output logic        adp_dmem_stall,
  output logic        adp_func_stall,
  output logic        adp_load_hazard,
  input  logic        adp_ctrl_stall
);
    
// Pipeline Stages
if_stage_t  if_stage_reg;
id_stage_t  id_stage_reg;
ex_stage_t  ex_stage_reg;
mem_stage_t mem_stage_reg;
wb_stage_t  wb_stage_reg;

// Stall Signals and Logic
logic i_id_reg_we;
logic pc_we;

// Indicates if the control unit / decoder has a compressed instruction
logic compressed;

// Flush Signals
logic branch_flush;
logic compressed_flush;

// Indicates that the processor should stall for instruction memory 
// in the current cycle. This current cycle, the processor does nothing.
logic imem_stall;
assign adp_imem_stall = imem_stall;

// Indicates that the processor should stall for data memory
// in the current cycle. This current cycle, the processor does nothing.
logic dmem_stall;
assign adp_dmem_stall = dmem_stall;

// Indicates that a multicycle functional unit is currently executing
logic func_stall;
assign adp_func_stall = func_stall;

// Indicates a load hazards that must be resolved by stalling fetch and decode
logic load_hazard;
assign adp_load_hazard = load_hazard;

// Combinational write enable signals
logic if_stall; 
logic id_stall; 
logic ex_stall; 
logic mem_stall;
logic wb_stall; 
assign if_stall  = imem_stall | dmem_stall | func_stall | adp_ctrl_stall | load_hazard;
assign id_stall  = imem_stall | dmem_stall | func_stall | adp_ctrl_stall;
assign ex_stall  = imem_stall | dmem_stall | func_stall | adp_ctrl_stall;
assign mem_stall = imem_stall | dmem_stall | func_stall | adp_ctrl_stall;
assign wb_stall  = imem_stall | dmem_stall | func_stall | adp_ctrl_stall;

pc_mux_t     pc_mux;
logic [31:0] pc_offset__; // FIXME: Extra __ because of Verilator

//Interrupt signal ogic
logic branch_interrupt_flag, compressed_int_flag;
logic end_int;
logic wb_int_flag;

assign interrupt_serviced = end_int;

if_stage if_stage0 (
  .clk                (clk),
  .rst                (rst),
  .i_compressed       (compressed),
  .i_signaled_int     (signal_interrupt),
  .i_end_int          (end_int),
  .i_int_PC           (interrupt_PC),
  .i_pc_mux           (pc_mux),
  .i_pc_offset        (pc_offset__),
  .i_branch_flush     (branch_flush),
  .i_branch_int       (branch_interrupt_flag),
  .i_compr_int        (compressed_int_flag),
  .o_int_accepted     (int_accepted),
  // .o_compressed_flush (compressed_flush),
  .if_stall           (if_stall),
  // .imem_resp          (imem_resp),
  .imem_addr          (imem_addr),
  .imem_rmask         (imem_rmask),
  .if_stage_reg       (if_stage_reg),
  .adp_wdata          (adp_wdata),
  .adp_pc_we          (adp_pc_we),
  .adp_core_pc        (adp_core_pc)
);

logic        wb_regf_we;
logic [4:0]  wb_rd_addr;
logic [31:0] wb_write_data;
id_stage id_stage0 (
  .clk                (clk),
  .rst                (rst),
  .o_compressed       (compressed), 
  .i_regf_we          (wb_regf_we),
  .i_rd_addr          (wb_rd_addr),
  .i_rd_wdata         (wb_write_data),
  .i_branch_flush     (branch_flush || end_int), //when mret, flush decode stage
  .i_branch_int       (branch_interrupt_flag),
  .o_compr_int_flag   (compressed_int_flag),
  // .i_compressed_flush (compressed_flush), 
  .id_stall           (id_stall),
  .ex_stall           (ex_stall),
  .imem_stall         (imem_stall),
  .load_hazard        (load_hazard),
  .imem_rmask         (imem_rmask),
  .imem_rdata         (imem_rdata),
  .imem_resp          (imem_resp),
  .i_start_interrupt  (signal_interrupt),
  .i_end_interrupt    (end_int),
  .i_wb_int_flag      (wb_int_flag),
  .if_stage_reg       (if_stage_reg),
  .id_stage_reg       (id_stage_reg),
  .adp_rd_addr        (adp_rd_addr),
  .adp_wdata          (adp_wdata),
  .adp_reg_we         (adp_reg_we),
  .adp_ir_we          (adp_ir_we),
  .adp_core_ir        (adp_core_ir),
  .adp_core_reg       (adp_core_reg)
);

ex_stage ex_stage0 (
  .clk            (clk),
  .rst            (rst),
  .o_pc_mux       (pc_mux),
  .o_pc_offset    (pc_offset__),
  .ex_stall       (ex_stall),
  .dmem_stall     (dmem_stall),
  .func_stall     (func_stall),
  .o_branch_flush (branch_flush),
  .o_branch_int   (branch_interrupt_flag),
  .o_end_int      (end_int),
  .i_wb_data      (wb_write_data),
  .id_stage_reg   (id_stage_reg),
  .mem_stage_reg  (mem_stage_reg),
  .ex_stage_reg   (ex_stage_reg)
);

mem_stage mem_stage0 (
  .clk           (clk),
  .rst           (rst),
  .mem_stall     (mem_stall),
  .dmem_addr     (dmem_addr),
  .dmem_rmask    (dmem_rmask),
  .dmem_wmask    (dmem_wmask),
  .dmem_wdata    (dmem_wdata),
  .ex_stage_reg  (ex_stage_reg),
  .mem_stage_reg (mem_stage_reg)
);

wb_stage wb_stage0 (
  .clk           (clk),
  .rst           (rst),
  .o_regf_we     (wb_regf_we),
  .o_rd_addr     (wb_rd_addr),
  .o_write_data  (wb_write_data),
  .wb_stall      (wb_stall),
  .dmem_stall    (dmem_stall),
  .o_wb_int_flag (wb_int_flag),
  .dmem_rdata    (dmem_rdata),
  .dmem_rmask    (dmem_rmask),
  .dmem_wmask    (dmem_wmask),
  .dmem_resp     (dmem_resp),
  .mem_stage_reg (mem_stage_reg),
  .wb_stage_reg  (wb_stage_reg)
);

// RVFI Specific Signals
logic        monitor_valid;
logic        monitor_int_valid;
logic [63:0] monitor_order;
logic [63:0] monitor_int_order;
logic [31:0] monitor_inst;
logic [4:0]  monitor_rs1_addr;
logic [4:0]  monitor_rs2_addr;
logic [31:0] monitor_rs1_rdata;
logic [31:0] monitor_rs2_rdata;
logic        monitor_regf_we;
logic [4:0]  monitor_rd_addr;
logic [31:0] monitor_rd_wdata;
logic [31:0] monitor_pc_rdata;
logic [31:0] monitor_pc_wdata;
logic [31:0] monitor_mem_addr;
logic [3:0]  monitor_mem_rmask;
logic [3:0]  monitor_mem_wmask;
logic [31:0] monitor_mem_rdata;
logic [31:0] monitor_mem_wdata;

// RVFI Valid Logic
logic new_order, new_int_order;
logic [63:0] rvfi_order_probe, rvfi_int_order_probe;
always_ff @(posedge clk, posedge rst) begin
  if (rst) begin
    rvfi_order_probe <= '1;
    rvfi_int_order_probe <= '1;
  end else begin
    if (wb_stage_reg.rvfi.valid) begin
      rvfi_order_probe <= wb_stage_reg.rvfi.order;
    end
    
    if (wb_stage_reg.rvfi.int_valid) begin
      rvfi_int_order_probe <= wb_stage_reg.rvfi.int_order;
    end
  end
end 

assign new_order = (rvfi_order_probe == wb_stage_reg.rvfi.order);
assign new_int_order = (rvfi_int_order_probe == wb_stage_reg.rvfi.int_order);

assign monitor_int_valid = (wb_stage_reg.rvfi.int_valid && !new_int_order);
assign monitor_valid     = (wb_stage_reg.rvfi.valid && !new_order); //and valid signal with inverted interrupt signal to shut off rvfi during ints
assign monitor_order     = wb_stage_reg.rvfi.order;
assign monitor_int_order = wb_stage_reg.rvfi.int_order;
assign monitor_inst      = wb_stage_reg.rvfi.inst;
assign monitor_rs1_addr  = wb_stage_reg.rvfi.rs1_addr;
assign monitor_rs2_addr  = wb_stage_reg.rvfi.rs2_addr;
assign monitor_rs1_rdata = wb_stage_reg.rvfi.rs1_rdata;
assign monitor_rs2_rdata = wb_stage_reg.rvfi.rs2_rdata;
assign monitor_rd_addr   = wb_stage_reg.rvfi.rd_addr;
assign monitor_rd_wdata  = wb_stage_reg.rvfi.rd_wdata;
assign monitor_pc_rdata  = wb_stage_reg.rvfi.pc_rdata;
assign monitor_pc_wdata  = wb_stage_reg.rvfi.pc_wdata;
assign monitor_mem_addr  = wb_stage_reg.rvfi.mem_addr;
assign monitor_mem_rmask = wb_stage_reg.rvfi.mem_rmask;
assign monitor_mem_wmask = wb_stage_reg.rvfi.mem_wmask;
assign monitor_mem_rdata = wb_stage_reg.rvfi.mem_rdata;
assign monitor_mem_wdata = wb_stage_reg.rvfi.mem_wdata;

endmodule : cpu
