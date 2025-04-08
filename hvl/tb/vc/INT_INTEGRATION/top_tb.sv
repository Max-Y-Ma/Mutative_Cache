import "DPI-C" function string getenv(input string env_name);



module top_tb;

timeunit 1ns;
timeprecision 1ps;

// Clock Generation
int clock_half_period_ps = getenv("ECE411_CLOCK_PERIOD_PS").atoi() / 2;
int clock_half_period_ns = clock_half_period_ps / 1000;

bit clk;
initial begin
  clk <= 0; // #0 nonblocking assignment ~ negedge clock event
  forever #(clock_half_period_ns) clk = ~clk;
end

//file write/comapare signals
int   fd_2;
logic file_write_flag;

// External Off-chip Reset
bit rst;
initial begin
  rst <= 1'b1; // #0 nonblocking assignment ~ posedge reset event driven on negedge clock
  @(posedge clk);
  @(negedge clk); // Deassert reset on negedge clock 
  rst = 1'b0;
end

localparam NUM_INTERRUPTS = 16;
localparam NUM_GPIO = 8;
localparam QSPI_DATA_WIDTH = 4;
localparam INTERRUPT_BITS = $clog2(NUM_INTERRUPTS);

  `include "Interrupt_coverage.svh"
  
  int clk_delay;

  RandInitPic gen_init = new();

// QSPI Flash Interface
qspi_itf qspi_itf0();

// Monitor Interface
mon_itf mon_itf(.clk(dut.cpu0.clk), .rst(dut.cpu0.rst));    
monitor monitor(.itf(mon_itf));

// Peripheral Interfaces
spi_itf spi_itf0();

i2c_itf i2c_itf0();
i2c_itf i2c_itf1();

uart_itf uart_itf0();
uart_itf uart_itf1();

gpio_itf #(.NUM_GPIO(NUM_GPIO)) gpio_itf0();
adp_itf adp_itf0();

// TODO: Change, just for bringup
initial begin
  adp_itf0.tck = '0;
  adp_itf0.tms = '0;
  adp_itf0.tdi = '0;
  // adp_itf0.tdo = '0; // This is output from DUT, we shouldn't drive these
  // adp_itf0.tst = '0;
end

// Memory Model
W25Q128JVxIQ flash(
  .CSn(qspi_itf0.csn),
  .CLK(qspi_itf0.clk),
  .DIO(qspi_itf0.io[0]),
  .DO(qspi_itf0.io[1]),
  .WPn(qspi_itf0.io[2]),
  .HOLDn(qspi_itf0.io[3])
);

// Pull-up on GPIO pins
assign (pull1, pull0) gpio_itf0.gpio = '1;

// DUT Instantiation
core #(
  .NUM_INTERRUPTS(NUM_INTERRUPTS),
  .NUM_GPIO(NUM_GPIO),
  .QSPI_DATA_WIDTH(QSPI_DATA_WIDTH)
) dut (
  .sys_clk_i_pin(clk),
  .sys_rst_i_pin(rst),
  .qspi_io_io_pin(qspi_itf0.io),
  .qspi_ck_o_pin(qspi_itf0.clk),
  .qspi_cs_o_pin(qspi_itf0.csn),
  .spi_miso_i_pin(spi_itf0.miso),
  .spi_cs_o_pin(spi_itf0.cs),
  .spi_sclk_o_pin(spi_itf0.sclk),
  .i2c1_sda_io_pin(i2c_itf0.sda),
  .i2c1_scl_o_pin(i2c_itf0.scl),
  .i2c2_sda_io_pin(i2c_itf1.sda),
  .i2c2_scl_o_pin(i2c_itf1.scl),
  .uart1_tx_o_pin(uart_itf0.tx),
  .uart1_rx_i_pin(uart_itf0.rx),
  .uart2_tx_o_pin(uart_itf1.tx),
  .uart2_rx_i_pin(uart_itf1.rx),
  .gpio_a_io_pin(gpio_itf0.gpio),
  .adp_tck_i_pin(adp_itf0.tck),
  .adp_tms_i_pin(adp_itf0.tms),
  .adp_tdi_i_pin(adp_itf0.tdi),
  .adp_tdo_o_pin(adp_itf0.tdo),
  .adp_tst_o_pin(adp_itf0.tst)
);

// Monitor Interface DUT Wiring
`include "../../chip/tb/vc/soc/rvfi_reference.svh"

// TODO: UVM Stuff


task signal_random_interrupts();

    if(~dut.in_service) begin
        gen_init.randomize();
        dut.interrupt_pins <= gen_init.rand_Interrupt_ID;

        repeat (1) @(posedge clk);
        dut.interrupt_pins <= '0;
        gen_init.latched_Interrupt_ID <= dut.interrupt_pins;

        repeat ($urandom_range(5,20)) @(posedge clk);
    end else begin  
        dut.interrupt_pins <= '0;
        repeat (1) @(posedge clk);
    end
endtask : signal_random_interrupts

task signal_random_single_interrupts();

    if(!dut.in_service) begin
        gen_init.randomize();
        dut.interrupt_pins <= gen_init.rand_single_Interrupt_ID;

        repeat (1) @(posedge clk);
        dut.interrupt_pins <= '0;
        
        repeat ($urandom_range(5,20)) @(posedge clk);

    end else begin  
        dut.interrupt_pins <= '0;
        repeat (1) @(posedge clk);
    end

endtask : signal_random_single_interrupts

logic [15:0] in_order_interrupts;
task signal_in_order_interrupts();

    //when an interrupt succesfully ends, then signal the next
    if(dut.cpu0.end_int && ~dut.cpu0.if_stall) begin
        gen_init.randomize();
        dut.interrupt_pins <= in_order_interrupts;

        if(in_order_interrupts == 1'b1) begin
          in_order_interrupts <= 16'h8000;

        repeat ($urandom_range(5,20)) @(posedge clk);
        end else begin
          in_order_interrupts <= (in_order_interrupts >> 1);
        end 

    end else if(dut.interrupt_pins != 'h0) 
      dut.interrupt_pins <= 16'h0000;
    else   
      dut.interrupt_pins <= 16'h8000;
    
    

endtask : signal_in_order_interrupts

task automatic sample_output_int_signal(input logic signal_interrupt, input logic[INTERRUPT_BITS-1:0]signal_int_id, ref logic [INTERRUPT_BITS-1:0] Interrupt_bins);

  if(signal_interrupt) begin
      Interrupt_bins = signal_int_id;
      gen_init.output_interrupts.sample();
  end

endtask : sample_output_int_signal
// Waveform Dumpfiles
initial begin
  dut.interrupt_pins            <= 16'h0000;
  in_order_interrupts           <= 16'h8000;
  gen_init.latched_Interrupt_ID <= '0;
  file_write_flag               <=  1'b0;

  $fsdbDumpfile("dump.fsdb");
  $fsdbDumpvars(0, top_tb.qspi_itf0);
  $fsdbDumpvars(0, top_tb.mon_itf);
  $fsdbDumpvars(0, top_tb.monitor);
  $fsdbDumpvars(0, top_tb.dut, "+all");
  // $fsdbDumpvars(0, top_tb.dut.cpu0, "+all");

  $dumpfile("dump.vcd");
  $dumpvars();
end


int timeout_cycles = 10000000;
always @(posedge clk) begin
  fork
  begin
    sample_output_int_signal(dut.cpu0.signal_interrupt, dut.interrupt_controller_a.signal_int_id, gen_init.signaled_Interrupt_ID);
  end 
  begin
    // signal_random_interrupts();
    // signal_random_single_interrupts();
    signal_in_order_interrupts();
  end
  begin
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
    timeout_cycles <= timeout_cycles - 1;
  end
  join_none
end

initial fd_2 = $fopen("/home/sgohil3/acadia/digital/sim/sim/int_commit.log", "w");
final $fclose(fd_2); 
  always @ (posedge clk) begin


      if(dut.cpu0.monitor_int_valid) begin
          if (dut.cpu0.monitor_int_order % 1000 == 0) begin
              $display("dut commit No.%d, rd_s: x%02d, rd: 0x%h", mon_itf.order, mon_itf.rd_addr, mon_itf.rd_addr ? mon_itf.rd_wdata : 5'd0);
          end
          if (mon_itf.inst[1:0] == 2'b11) begin
              $fwrite(fd_2, "core   0: 3 0x%h (0x%h)", mon_itf.pc_rdata, mon_itf.inst);
          end else begin
              $fwrite(fd_2, "core   0: 3 0x%h (0x%h)", mon_itf.pc_rdata, mon_itf.inst[15:0]);
          end
          if (mon_itf.rd_addr != 0) begin
              if (mon_itf.rd_addr < 10)
                  $fwrite(fd_2, " x%0d  ", mon_itf.rd_addr);
              else
                  $fwrite(fd_2, " x%0d ", mon_itf.rd_addr);
              $fwrite(fd_2, "0x%h", mon_itf.rd_wdata);
          end
          if (mon_itf.mem_rmask != 0) begin
              automatic int first_1 = 0;
              for(int i = 0; i < 4; i++) begin
                  if(mon_itf.mem_rmask[i]) begin
                      first_1 = i;
                      break;
                  end
              end
              $fwrite(fd_2, " mem 0x%h", {mon_itf.mem_addr[31:2], 2'b0} + first_1);
          end
          if (mon_itf.mem_wmask != 0) begin
              automatic int amount_o_1 = 0;
              automatic int first_1 = 0;
              for(int i = 0; i < 4; i++) begin
                  if(mon_itf.mem_wmask[i]) begin
                      amount_o_1 += 1;
                  end
              end
              for(int i = 0; i < 4; i++) begin
                  if(mon_itf.mem_wmask[i]) begin
                      first_1 = i;
                      break;
                  end
              end
              $fwrite(fd_2, " mem 0x%h", {mon_itf.mem_addr[31:2], 2'b0} + first_1);
              case (amount_o_1)
                  1: begin
                      automatic logic[7:0] wdata_byte = mon_itf.mem_wdata[8*first_1 +: 8];
                      $fwrite(fd_2, " 0x%h", wdata_byte);
                  end
                  2: begin
                      automatic logic[15:0] wdata_half = mon_itf.mem_wdata[8*first_1 +: 16];
                      $fwrite(fd_2, " 0x%h", wdata_half);
                  end
                  4:
                      $fwrite(fd_2, " 0x%h", mon_itf.mem_wdata);
              endcase
          end
          $fwrite(fd_2, "\n");
      end
  end

endmodule : top_tb
