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
  #100; // Wait before turning on clock
  forever #(clock_half_period_ns) clk = ~clk;
end

// External Off-chip Reset
bit rst;
initial begin
  rst <= 1'b1;    // #0 nonblocking assignment ~ posedge reset event
  #33 rst = 1'b0; // Model asynchronous deassert
end

localparam NUM_INTERRUPTS = 16;
localparam NUM_GPIO = 8;
localparam QSPI_DATA_WIDTH = 4;

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

logic       adc_clk;
logic       adc_rst_sync;
logic       adc_eoc_n;        // Input
logic [7:0] adc_data;         // Input
logic       adc_firmware_en;
logic       adc_adc_en;
logic       adc_calib_en;
logic       adc_ext_opt;
logic [7:0] dac_reg;

initial begin
  adc_eoc_n <= '1;
  adc_data  <= 8'hxx;

  #1000

  @(posedge dac_reg[0]);

  @(posedge adc_clk);

  adc_eoc_n <= '0;
  adc_data  <= 8'h55;

  @(posedge adc_clk);
  adc_eoc_n <= '1;
  adc_data  <= 8'hxx;

  repeat(730) @(posedge adc_clk);

  adc_eoc_n <= '0;
  adc_data  <= 8'hAA;

  @(posedge adc_clk);
  adc_eoc_n <= '1;
  adc_data  <= 8'hxx;
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

// Pull-up on I2C pins
assign (pull1, pull0) i2c_itf0.sda = '1;
assign (pull1, pull0) i2c_itf1.sda = '1;

// I2C Slave
i2c_slave_model #(7'b010_0000) i2c0_slave0 (
  .scl(i2c_itf0.scl),
  .sda(i2c_itf0.sda)
);

i2c_slave_model #(7'b011_0000) i2c0_slave1 (
  .scl(i2c_itf0.scl),
  .sda(i2c_itf0.sda)
);

i2c_slave_model #(7'b010_0000) i2c01_slave0 (
  .scl(i2c_itf1.scl),
  .sda(i2c_itf1.sda)
);

i2c_slave_model #(7'b011_0000) i2c1_slave1 (
  .scl(i2c_itf1.scl),
  .sda(i2c_itf1.sda)
);

// Pull-up on GPIO pins
assign (pull1, pull0) gpio_itf0.gpio = '1;

// UART loopbacks
assign uart_itf0.rx = uart_itf0.tx;
assign uart_itf1.rx = uart_itf1.tx;

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
  .spi_mosi_o_pin(spi_itf0.mosi),
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
  .adp_tst_o_pin(adp_itf0.tst),

  /* Analog Internal Interface */
  .adc_clk(adc_clk),
  .adc_rst_sync(adc_rst_sync),
  .adc_eoc_n(adc_eoc_n),
  .adc_data(adc_data),
  .adc_firmware_en(adc_firmware_en),
  .adc_adc_en(adc_adc_en),
  .adc_calib_en(adc_calib_en),
  .adc_ext_opt(adc_ext_opt),

  .dac_reg(dac_reg)
);

// Monitor Interface DUT Wiring
`include "../../chip/tb/vc/soc/rvfi_reference.svh"

// Run Tests
bit test_halt;

`ifdef ADP_TEST
  run_adp_test run_adp_test0(.adp_if(adp_itf0), .test_halt(test_halt));

  always_ff @(posedge clk) begin
    if (test_halt) $finish;
  end
`else
  assign test_halt = 1'b1;
`endif

// Waveform Dumpfiles
initial begin
  $fsdbDumpfile("dump.fsdb");
  // $fsdbDumpvars(0, "+all");
  $fsdbDumpvars(0, top_tb.qspi_itf0);
  $fsdbDumpvars(0, top_tb.mon_itf);
  $fsdbDumpvars(0, top_tb.monitor);
  $fsdbDumpvars(0, top_tb.dut);

  // $dumpfile("dump.vcd");
  // $dumpvars();
end

// Core Dump
localparam CORE_DUMP_GPIO_VALUE = 'h69;

int core_fd;
initial core_fd = $fopen("./core.log", "w");
final $fclose(core_fd);
logic [31:0] tmp_buf;

logic [3:0] prev_dmem_rmask, prev_dmem_wmask;
logic [31:0] prev_dmem_addr, prev_dmem_wdata;

always @(posedge clk) begin
  // Dump all D-sram transactions
  prev_dmem_rmask <= dut.data_memory0.dmem_rmask;
  prev_dmem_wmask <= dut.data_memory0.dmem_wmask;

  prev_dmem_addr  <= dut.data_memory0.dmem_addr;
  prev_dmem_wdata <= dut.data_memory0.dmem_wdata;

  if(dut.data_memory0.dmem_resp) begin
    if(|prev_dmem_rmask) begin
      $fwrite(core_fd, "DMEM R (%04b): 0x%08H 0x%08H @ %t\n", prev_dmem_rmask, prev_dmem_addr, dut.data_memory0.dmem_rdata, $time);
    end else if(|prev_dmem_wmask) begin
      $fwrite(core_fd, "DMEM W (%04b): 0x%08H 0x%08H @ %t\n", prev_dmem_wmask, prev_dmem_addr, prev_dmem_wdata, $time);
    end
  end

  if ((gpio_itf0.gpio == CORE_DUMP_GPIO_VALUE) && test_halt) begin
    // Log Core Registers
    // For non-gatelevel, adp_core_reg includes reg 0, so we need to skip
    for (int i = 1; i < 32; i++) begin
      $fwrite(core_fd, "X%0H: 0x%0H\n", (i), (dut.adp_core_reg[i]));
    end

    // Log Core Program Counter
    $fwrite(core_fd, "PC: 0x%0H\n", dut.adp_core_pc);

    $fwrite(core_fd, "End Time: %t\n", $time);

    $fwrite(core_fd, "D-SRAM Dump:\n");
    for(int i = 0; i < 256; ++i) begin
      $fwrite(core_fd, "0x%02H: ", (i));
      for(int mux = 0; mux < 8; ++mux) begin
        for(int cntr = 0; cntr < 32; ++cntr) begin
         tmp_buf[cntr] = dut.data_memory0.data_sram0.mem[i][mux+cntr*8];
        end

        $fwrite(core_fd, "%08h", tmp_buf);
      end
      $fwrite(core_fd, "\n");
    end

    $finish;
  end
end

// End Conditions
int timeout_cycles = 10000000;
always @(posedge clk) begin
  if (mon_itf.halt && test_halt) begin
    $finish;
  end
  if (timeout_cycles == 0 && test_halt) begin
    $error("TB Error: Timed out");
    $finish;
  end
  if (mon_itf.error != 0 && test_halt) begin
    repeat (5) @(posedge clk);
    $finish;
  end
  if(timeout_cycles % 1_000 == 0) begin
    $display("Time %t", $time);
  end
  timeout_cycles <= timeout_cycles - 1;
end

endmodule : top_tb
