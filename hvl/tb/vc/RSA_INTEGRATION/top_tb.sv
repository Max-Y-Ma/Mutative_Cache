`ifdef RANDOM
  `include "cpu_pkg.svh"
`endif

module top_tb;

  timeunit 1ps;
  timeprecision 1ps;

  // Clock Generation
  `define CLK_HALF_PERIOD (5)
  bit clk;
  always #(`CLK_HALF_PERIOD) clk = ~clk;

  bit rst;

  logic [4:0]  adp_rd_addr;
  logic [31:0] adp_wdata;
  logic        adp_reg_we;
  logic        adp_pc_we;
  logic        adp_ir_we;
  logic        adp_ctrl_stall;

  assign adp_ctrl_stall  = '0;
  assign adp_rd_addr     = '0;
  assign adp_wdata       = '0;
  assign adp_pc_we       = '0;  
  assign adp_ir_we       = '0;

  logic        start_RSA, RSA_idle;
  logic        update_key, update_mod_n, update_msg_blk;
  logic [15:0] RSA_output_msg;

  // logic [31:0] imem_addr;
  // logic [3:0]  imem_rmask;
  // logic        imem_resp;
  // logic [31:0] imem_rdata;

  logic [31:0] dmem_addr;
  logic [3:0]  dmem_rmask;
  logic [3:0]  dmem_wmask;
  logic        dmem_resp;
  logic [31:0] dmem_rdata;
  logic [31:0] dmem_wdata;

  mem_itf mem_itf_i(.clk(clk), .rst(rst));
  mem_itf mem_itf_d(.clk(clk), .rst(rst));
  ordinary_dual_port mem(.itf_i(mem_itf_i), .itf_d(mem_itf_d));

  // Monitor Interface
  mon_itf mon_itf(.*);    
  monitor monitor(.itf(mon_itf));

 // DUT Instantiation
  cpu dut(
    .clk            (clk),
    .rst            (rst),

    // Instruction Memory Port
    .imem_addr      (mem_itf_i.addr),
    .imem_rmask     (mem_itf_i.rmask),
    .imem_rdata     (mem_itf_i.rdata),
    .imem_resp      (mem_itf_i.resp),

    // Data Memory Port
    .dmem_addr      (dmem_addr),
    .dmem_rmask     (dmem_rmask),
    .dmem_wmask     (dmem_wmask),
    .dmem_rdata     (dmem_rdata),
    .dmem_wdata     (dmem_wdata),
    .dmem_resp      (dmem_resp),

      // ADP debug signal interface
    .adp_core_reg(),
    .adp_core_pc(),
    .adp_core_ir(),
    .adp_rd_addr(adp_rd_addr),
    .adp_wdata(adp_wdata),
    .adp_reg_we(),
    .adp_pc_we(adp_pc_we),
    .adp_ir_we(adp_ir_we),
    .adp_imem_stall(adp_imem_stall),
    .adp_dmem_stall(adp_dmem_stall),
    .adp_func_stall(adp_func_stall),
    .adp_load_hazard(adp_load_hazard),
    .adp_ctrl_stall(adp_ctrl_stall)
  );

  RSA_ACCELERATOR dut_RSA(
    .clk(clk),
    .rst_n(~rst),
    .RSA_start(start_RSA),

    .RSA_key(dmem_wdata[15:0]),
    .mod_n(dmem_wdata[15:0]),
    .msg_block(dmem_wdata[15:0]),

    .update_key_from_mem(update_key),
    .update_mod_n(update_mod_n),
    .update_msg_blk(update_msg_blk),

    .o_output_msg(RSA_output_msg),
    .o_idle_flag(RSA_idle)
  );

  mem_map_decoder mem_map_decoder0(
    .clk(clk),
    .rst(rst),

    .dmem_addr(dmem_addr),
    .dmem_rmask(dmem_rmask),
    .dmem_wmask(dmem_wmask),
    .dmem_rdata(dmem_rdata),
    .dmem_wdata(dmem_wdata),
    .dmem_resp(dmem_resp),

    /* DFP to Data SRAM */
    .data_memory0_addr(mem_itf_d.addr),
    .data_memory0_rmask(mem_itf_d.rmask),
    .data_memory0_wmask(mem_itf_d.wmask),
    .data_memory0_rdata(mem_itf_d.rdata),
    .data_memory0_wdata(mem_itf_d.wdata),
    .data_memory0_resp(mem_itf_d.resp),

    /* DFP to GPIO drivers */
    .gpio_a_addr(),
    .gpio_a_rmask(),
    .gpio_a_wmask(),
    .gpio_a_rdata(),
    .gpio_a_wdata(),
    .gpio_a_resp(),

    /* DFP to clock prescalers */
    .prescaler_rmask(),
    .prescaler_wmask(),
    .prescaler_rdata(),

    /*DFP to Interrupt Controller*/
    .intr_mask_val(),
    .read_int_mask(),
    .update_int_mask(),

    .int_vec_table_pc(),
    .read_vec_table(),
    .update_int_vec_table(),
    .int_table_entry_id(),



    /*DFP to RSA */
    .RSA_output_msg(RSA_output_msg),
    .start_RSA(start_RSA),
    .RSA_idle_flag(RSA_idle),
    .update_key(update_key),
    .update_mod_n(update_mod_n),
    .update_msg_blk(update_msg_blk),

    .adp_dmem_rdata(),
    .adp_dmem_addr(),
    .adp_dmem_rmask(),
    .adp_dmem_wmask(),
    .adp_dmem_wdata(),
    .adp_debug_mode()
  );

  logic [15:0] e, result, cmp_msg;
  logic [31:0] intermediate_res, intermediate_mes;
  logic [15:0] golden_msg, golden_mod;
  
  task calc_golden_msg(input [15:0] golden_key, golden_message, golden_mod_n);
      
      e       <= golden_key;
      cmp_msg <= golden_message;
      golden_mod <= golden_mod_n;

      intermediate_res  <= '0;
      intermediate_mes  <= '0;

      @(posedge clk);
      result  <= 1'b1;
      @(posedge clk);

      while(e != '0) begin
          
          if(e[0] == 1'b1) begin
              intermediate_res = result * cmp_msg;
              result           = intermediate_res % golden_mod;
          end

          intermediate_mes = cmp_msg * cmp_msg;
          cmp_msg          = intermediate_mes % golden_mod;

          e = e >> 1;
          @(posedge clk);
      end

      golden_msg <= result;

  endtask

  // Monitor Interface DUT Wiring
  `include "../../chip/tb/vc/cpu/rvfi_reference.svh"
  // Waveform Dumpfiles and Reset
  initial begin
    $fsdbDumpfile("dump.fsdb");
    $fsdbDumpvars(0, "+all");
    rst = 1'b1;
    repeat (2) @(posedge clk);
    rst <= 1'b0;

    fork //CPU thread to randomly send back interrupt serviced request if interrupt started
        forever begin
        repeat(1) @(posedge clk);
        if(start_RSA) begin
          calc_golden_msg(dut_RSA.stored_key, dut_RSA.bin_mes, dut_RSA.saved_mod_n);
        end else begin
          if (dut_RSA.idle_flag) begin
            if(golden_msg != dut_RSA.output_msg) begin
                $error("TB Error: Value Mismatch");
                $finish;
            end 

            if(golden_msg == dut_RSA.output_msg) begin
                // $display("value match: success");
            end
          end

        end
        
        end
      join_none
  end

  // End Condition
  int timeout_cycles = 10000000;
  always @(posedge clk) begin
    
    if (mon_itf.halt) begin
      $finish;
    end
    if (timeout_cycles == 0) begin
      $error("TB Error: Timed out");
      $finish;
    end
    if (mon_itf.error != 0) begin
      repeat (5) @(posedge clk);
      $finish;
    end
    if (mem_itf_i.error != 0) begin
      repeat (5) @(posedge clk);
      $finish;
    end
    if (mem_itf_d.error != 0) begin
      repeat (5) @(posedge clk);
      $finish;
    end
    timeout_cycles <= timeout_cycles - 1;
  end

endmodule : top_tb
