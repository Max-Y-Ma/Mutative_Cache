////////////////////////////////////////////////////////////////////////////////
// FIXME: Figure out total pin list on digital side
// 48 Digital Pin Map:
// -----------------------------------------------------------------------------
// 9 POWER PINS:
// x1 - VREF_TEST
// x1 - VREF_BIAS
// x1 - VRES
// x1 - VREF_EXT
// x1 - VDDa
// x1 - VSSa
// x2 - VDD
// x1 - GND
// -----------------------------------------------------------------------------
// 34 DIGITAL PINS:
// x1 - CLK
// x1 - RST
// x6 - QSPI (Q0, Q1, Q2, Q3, CS, SCLK)
// x2 - SPI (MOSI, SCLK)
// x2 - I2C1 (SDA, SCL)
// x2 - I2C2 (SDA, SCL)
// x2 - UART1 (TX, RX)
// x2 - UART2 (TX, RX)
// x8 - GPIO 
// x8 - ADP
// -----------------------------------------------------------------------------
// 5 ANALOG PINS:
// x1 - DACn
// x1 - DACp
// x1 - DAC_sigma_delta
// x1 - ADCn
// x1 - ADCp
// 
////////////////////////////////////////////////////////////////////////////////
module core
#(
  /*Interrupt Parameters */
  parameter NUM_INTERRUPTS = 16,
  parameter NUM_GPIO = 8,
  parameter QSPI_DATA_WIDTH = 4
)(
  /* Digital Clock Pin */
  input  logic sys_clk_i_pin,

  /* Digital Async Reset Pin */
  input  logic sys_rst_i_pin,

  /* QSPI Flash Interface Pins */
  inout        [3:0] qspi_io_io_pin,
  output logic       qspi_ck_o_pin,
  output logic       qspi_cs_o_pin,

  /* SPI Interface Pins */
  output logic spi_mosi_o_pin,
  output logic spi_sclk_o_pin,

  /* I2C1 Interface Pins */
  inout  wire  i2c1_sda_io_pin,
  output logic i2c1_scl_o_pin,

  /* I2C2 Interface Pins */
  inout  wire  i2c2_sda_io_pin,
  output logic i2c2_scl_o_pin,

  /* UART1 Interface Pins */
  output logic uart1_tx_o_pin,
  input  logic uart1_rx_i_pin,

  /* UART2 Interface Pins */
  output logic uart2_tx_o_pin,
  input  logic uart2_rx_i_pin,

  /* GPIO Pins */
  inout  wire [NUM_GPIO-1:0] gpio_a_io_pin,
  
  /* Acadia Debug Port Pins */
  input  logic       adp_tck_i_pin,
  input  logic       adp_tms_i_pin,
  input  logic       adp_tdi_i_pin,
  output logic       adp_tdo_o_pin,
  output logic [3:0] adp_tst_o_pin,

  /* ADC Register Interface */
  output logic        adc_clk,
  output logic        adc_rst_sync,
  input  logic        adc_eoc_n,  // End of Conversation
  input  logic [7:0]  adc_data, 
  output logic        adc_firmware_en,
  output logic        adc_adc_en,
  output logic        adc_calib_en,
  output logic        adc_ext_opt,

  /* DAC Register Interface */
  output logic [7:0] dac_reg
);

/* Peripheral Parameters */
localparam NUM_ADP_STATES = 4;
localparam INTERRUPT_BITS  = $clog2(NUM_INTERRUPTS); 
localparam KEY_SIZE_LEN = 16;

/* Cache Parameters */
localparam ICACHE_SETS = 256;
localparam ICACHE_CACHELINE = 64;

/* Data Memory Parameters */
localparam DMEM_WORDS = 2048;
localparam DMEM_WORDSIZE = 32;

logic           cpu_clk;
logic           cpu_main_clk;
logic           spi_clk;
logic           i2c1_clk;
logic           i2c2_clk;
logic           uart1_clk;
logic           uart2_clk;

logic           sys_rst_sync;
logic           adp_trst_sync;
logic           cpu_rst_sync;
logic           spi_rst_sync;
logic           i2c1_rst_sync;
logic           i2c2_rst_sync;
logic           uart1_rst_sync;
logic           uart2_rst_sync;

/* ADP debug signals */
logic           adp_imem_stall;
logic           adp_dmem_stall;
logic           adp_func_stall;
logic           adp_load_hazard;
logic           adp_ctrl_stall;

logic           adp_scan_end;
logic           adp_scan_enable;
logic           adp_scan_start;

logic           adp_bscan_end;
logic           adp_bscan_se;
logic           adp_bscan_oe;
logic           adp_bscan_shift_sel;
logic           adp_bscan_out_sel;
logic           adp_bscan_start;

logic   [31:0]  adp_core_reg [32];
logic   [31:0]  adp_core_pc;
logic   [31:0]  adp_core_ir;
logic   [31:0]  adp_core_adc;
logic   [31:0]  adp_core_dac;

logic   [4:0]   adp_rd_addr;
logic   [31:0]  adp_wdata;
logic           adp_reg_we;
logic           adp_pc_we;
logic           adp_ir_we;
logic           adp_adc_we;
logic           adp_dac_we;

logic   [31:0]  adp_dmem_rdata;
logic   [31:0]  adp_dmem_addr;
logic   [3:0]   adp_dmem_rmask;
logic   [3:0]   adp_dmem_wmask;
logic   [31:0]  adp_dmem_wdata;

logic           adp_debug_mode;

logic           sys_clk_i_buf;
logic           sys_rst_i_buf;

logic   [31:0]  icache_addr;
logic           icache_read;
logic           icache_write;
logic   [63:0]  icache_rdata;
logic   [63:0]  icache_wdata;
logic           icache_resp;

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

logic   [31:0]  data_memory0_addr;
logic   [3:0]   data_memory0_rmask;
logic   [3:0]   data_memory0_wmask;
logic   [31:0]  data_memory0_rdata;
logic   [31:0]  data_memory0_wdata;
logic           data_memory0_resp;

logic   [31:0]  gpio_a_addr;
logic   [3:0]   gpio_a_rmask;
logic   [3:0]   gpio_a_wmask;
logic   [31:0]  gpio_a_rdata;
logic   [31:0]  gpio_a_wdata;
logic           gpio_a_resp;

logic   [31:0]  uart1_addr;
logic   [3:0]   uart1_rmask;
logic   [3:0]   uart1_wmask;
logic   [31:0]  uart1_rdata;
logic   [31:0]  uart1_wdata;
logic           uart1_resp;

logic   [31:0]  uart2_addr;
logic   [3:0]   uart2_rmask;
logic   [3:0]   uart2_wmask;
logic   [31:0]  uart2_rdata;
logic   [31:0]  uart2_wdata;
logic           uart2_resp;

logic   [31:0]  i2c1_addr;
logic   [3:0]   i2c1_rmask;
logic   [3:0]   i2c1_wmask;
logic   [31:0]  i2c1_rdata;
logic   [31:0]  i2c1_wdata;
logic           i2c1_resp;

logic   [31:0]  i2c2_addr;
logic   [3:0]   i2c2_rmask;
logic   [3:0]   i2c2_wmask;
logic   [31:0]  i2c2_rdata;
logic   [31:0]  i2c2_wdata;
logic           i2c2_resp;

logic   [31:0]  spi1_addr;
logic   [3:0]   spi1_rmask;
logic   [3:0]   spi1_wmask;
logic   [31:0]  spi1_rdata;
logic   [31:0]  spi1_wdata;
logic           spi1_resp;

logic   [31:0]  analog_addr;
logic   [3:0]   analog_rmask;
logic   [3:0]   analog_wmask;
logic   [31:0]  analog_rdata;
logic   [31:0]  analog_wdata;

logic   [3:0]   qspi_io_i_buf;
logic   [3:0]   qspi_io_i;
logic   [3:0]   qspi_io_o_buf;
logic   [3:0]   qspi_io_o;
logic           qspi_io_t_buf;
logic           qspi_io_t;
logic           qspi_ck_o_buf;
logic           qspi_ck_o;
logic           qspi_cs_o_buf;
logic           qspi_cs_o;

logic           spi_mosi_o_buf;
logic           spi_mosi_o;
logic           spi_sclk_o_buf;
logic           spi_sclk_o;

logic           i2c1_sda_i_buf;
logic           i2c1_sda_i;
logic           i2c1_sda_o_buf;
logic           i2c1_sda_o;
logic           i2c1_sda_t_buf;
logic           i2c1_sda_t;
logic           i2c1_scl_o_buf;
logic           i2c1_scl_o;

logic           i2c2_sda_i_buf;
logic           i2c2_sda_i;
logic           i2c2_sda_o_buf;
logic           i2c2_sda_o;
logic           i2c2_sda_t_buf;
logic           i2c2_sda_t;
logic           i2c2_scl_o_buf;
logic           i2c2_scl_o;

logic           uart1_tx_o_buf;
logic           uart1_tx_o;
logic           uart1_rx_i_buf;
logic           uart1_rx_i;

logic           uart2_tx_o_buf;
logic           uart2_tx_o;
logic           uart2_rx_i_buf;
logic           uart2_rx_i;

logic   [NUM_GPIO-1:0]   gpio_a_i_buf;
logic   [NUM_GPIO-1:0]   gpio_a_i;
logic   [NUM_GPIO-1:0]   gpio_a_o_buf;
logic   [NUM_GPIO-1:0]   gpio_a_o;
logic   [NUM_GPIO-1:0]   gpio_a_t_buf;
logic   [NUM_GPIO-1:0]   gpio_a_t;

logic           adp_tck_i_buf;
logic           adp_tms_i_buf;
logic           adp_tdi_i_buf;
logic           adp_tfunc_i_buf;
logic           adp_tdo_o_buf;
logic   [3:0]   adp_tst_o_buf;

logic   [3:0]   prescaler_rmask;
logic   [3:0]   prescaler_wmask;
logic   [31:0]  prescaler_rdata;

logic   [15:0]  RSA_output_msg;
logic           start_RSA, update_key, update_mod_n, update_msg_blk;
logic           RSA_idle;

// FIXME
logic [NUM_INTERRUPTS-1:0] interrupt_pins;
logic in_service;

logic uart1_int_req;
logic uart2_int_req;
logic i2c1_int_req;
logic i2c2_int_req;
logic dac_interrupt;
logic adc_eoc_2ff;

assign interrupt_pins = {gpio_a_i[0], spi_clk, adc_eoc_2ff, dac_interrupt,
                        i2c2_int_req, i2c1_int_req, uart2_int_req, uart1_int_req,
                         gpio_a_i};

//interrupt read/write mask signals
logic                      int_read_mask, update_int_mask;
logic [NUM_INTERRUPTS-1:0] int_mask_val;


//interrupt read/write vector signals
logic                      read_vec_table, update_int_vec_table;
logic [INTERRUPT_BITS-1:0] table_entry_id;
logic [31:0]               int_vec_read_pc;

//cpu<--> Interrupt signals
logic                      interrupt_serviced;
logic [31:0]               interrupt_PC;
logic                      signal_interrupt;
logic                      int_accepted;

// I2C output
logic SDA1, SDA2;

////////////////////////////////////////////////////////////////////////////////
// In, Out, Tri Buffers
////////////////////////////////////////////////////////////////////////////////

// Clock Input Buffer
io_in ext_clk_buf (.chipout(sys_clk_i_pin), .chipin(sys_clk_i_buf));

// Reset Input Buffer
io_in ext_rst_buf (.chipout(sys_rst_i_pin), .chipin(sys_rst_i_buf));

// QSPI Data Tristate Buffers
generate 
  for(genvar i = 0; i < QSPI_DATA_WIDTH; ++i) begin
    io_tri qspi_io_buf(
      .chipout(qspi_io_io_pin[i]),
      .i(qspi_io_i_buf[i]),
      .o(qspi_io_o_buf[i]),
      .t(qspi_io_t_buf)
    );
  end
endgenerate

// QSPI Clock Output Buffer
io_out qspi_ck_buf (.chipout(qspi_ck_o_pin), .chipin(qspi_ck_o_buf));

// QSPI Chip Select Output Buffer
io_out qspi_cs_buf (.chipout(qspi_cs_o_pin), .chipin(qspi_cs_o_buf));

// SPI Interface Buffers
io_out spi_mosi_buf (.chipout(spi_mosi_o_pin), .chipin(spi_mosi_o_buf));
io_out spi_sclk_buf (.chipout(spi_sclk_o_pin), .chipin(spi_sclk_o_buf));

// I2C1 Interface Buffers
io_tri i2c1_sda_buf (
  .chipout(i2c1_sda_io_pin),
  .i(i2c1_sda_i_buf),
  .o(i2c1_sda_o_buf),
  .t(i2c1_sda_t_buf)
);
io_out i2c1_scl_buf (.chipout(i2c1_scl_o_pin), .chipin(i2c1_scl_o_buf));

// I2C2 Interface Pins
io_tri i2c2_sda_buf (
  .chipout(i2c2_sda_io_pin),
  .i(i2c2_sda_i_buf),
  .o(i2c2_sda_o_buf),
  .t(i2c2_sda_t_buf)
);
io_out i2c2_scl_buf (.chipout(i2c2_scl_o_pin), .chipin(i2c2_scl_o_buf));

// UART1 Interface Pins
io_out uart1_tx_buf (.chipout(uart1_tx_o_pin), .chipin(uart1_tx_o_buf));
io_in  uart1_rx_buf (.chipout(uart1_rx_i_pin), .chipin(uart1_rx_i_buf));

// UART2 Interface Pins
io_out uart2_tx_buf (.chipout(uart2_tx_o_pin), .chipin(uart2_tx_o_buf));
io_in  uart2_rx_buf (.chipout(uart2_rx_i_pin), .chipin(uart2_rx_i_buf));

// GPIO Tristate Buffers
generate 
  for(genvar i = 0; i < NUM_GPIO; ++i) begin
    io_tri gpio_a_buf (
      .chipout(gpio_a_io_pin[i]),
      .i(gpio_a_i_buf[i]),
      .o(gpio_a_o_buf[i]),
      .t(gpio_a_t_buf[i])
    );
  end
endgenerate

// Acadia Debug Port Buffers
io_in  adp_tck_buf   (.chipout(adp_tck_i_pin),   .chipin(adp_tck_i_buf));
io_in  adp_tms_buf   (.chipout(adp_tms_i_pin),   .chipin(adp_tms_i_buf));
io_in  adp_tdi_buf   (.chipout(adp_tdi_i_pin),   .chipin(adp_tdi_i_buf));
io_out adp_tdo_buf   (.chipout(adp_tdo_o_pin),   .chipin(adp_tdo_o_buf));

generate 
  for(genvar i = 0; i < NUM_ADP_STATES; ++i) begin
    io_out adp_tst_buf (
      .chipout(adp_tst_o_pin[i]),
      .chipin(adp_tst_o_buf[i])
    );
  end
endgenerate

////////////////////////////////////////////////////////////////////////////////
// Core Clock and Reset Controller
////////////////////////////////////////////////////////////////////////////////

core_ctrl core_ctrl0 (
  .sys_clk(sys_clk_i_buf),
  .sys_rst(sys_rst_i_buf),

  /* Dmem Interface */
  .dmem_addr(dmem_addr),
  .dmem_rmask(prescaler_rmask),
  .dmem_wmask(prescaler_wmask),
  .dmem_wdata(dmem_wdata),
  .prescaler_rdata(prescaler_rdata),

  /* Generated clocks */
  .cpu_clk(cpu_clk),
  .spi_clk(spi_clk),
  .i2c1_clk(i2c1_clk),
  .i2c2_clk(i2c2_clk),
  .uart1_clk(uart1_clk),
  .uart2_clk(uart2_clk),
  .adc_clk(adc_clk),

  /* Generated resets */
  .sys_rst_sync(sys_rst_sync),
  .adp_trst_sync(adp_trst_sync),
  .cpu_rst_sync(cpu_rst_sync),
  .spi_rst_sync(spi_rst_sync),
  .i2c1_rst_sync(i2c1_rst_sync),
  .i2c2_rst_sync(i2c2_rst_sync),
  .uart1_rst_sync(uart1_rst_sync),
  .uart2_rst_sync(uart2_rst_sync),
  .adc_rst_sync(adc_rst_sync)
);

////////////////////////////////////////////////////////////////////////////////
// Acadia Debug Port
////////////////////////////////////////////////////////////////////////////////

// Boundary Scan Module
adp_boundary_scan adp_boundary_scan0 (
  .adp_bscan_clk(adp_tck_i_buf),
  .adp_bscan_rst(adp_trst_sync),
  .adp_bscan_start(adp_bscan_start),
  .adp_bscan_se(adp_bscan_se),
  .adp_bscan_oe(adp_bscan_oe),
  .adp_bscan_shift_sel(adp_bscan_shift_sel),
  .adp_bscan_out_sel(adp_bscan_out_sel),
  .adp_bscan_end(adp_bscan_end),
  .qspi_io_i_buf(qspi_io_i_buf),
  .qspi_io_i(qspi_io_i),
  .qspi_io_o_buf(qspi_io_o_buf),
  .qspi_io_o(qspi_io_o),
  .qspi_io_t_buf(qspi_io_t_buf),
  .qspi_io_t(qspi_io_t),
  .qspi_ck_o_buf(qspi_ck_o_buf),
  .qspi_ck_o(qspi_ck_o),
  .qspi_cs_o_buf(qspi_cs_o_buf),
  .qspi_cs_o(qspi_cs_o),
  .spi_mosi_o_buf(spi_mosi_o_buf),
  .spi_mosi_o(spi_mosi_o),
  .spi_sclk_o_buf(spi_sclk_o_buf),
  .spi_sclk_o(spi_sclk_o),
  .i2c1_sda_i_buf(i2c1_sda_i_buf),
  .i2c1_sda_i(i2c1_sda_i),
  .i2c1_sda_o_buf(i2c1_sda_o_buf),
  .i2c1_sda_o(i2c1_sda_o),
  .i2c1_sda_t_buf(i2c1_sda_t_buf),
  .i2c1_sda_t(i2c1_sda_t),
  .i2c1_scl_o_buf(i2c1_scl_o_buf),
  .i2c1_scl_o(i2c1_scl_o),
  .i2c2_sda_i_buf(i2c2_sda_i_buf),
  .i2c2_sda_i(i2c2_sda_i),
  .i2c2_sda_o_buf(i2c2_sda_o_buf),
  .i2c2_sda_o(i2c2_sda_o),
  .i2c2_sda_t_buf(i2c2_sda_t_buf),
  .i2c2_sda_t(i2c2_sda_t),
  .i2c2_scl_o_buf(i2c2_scl_o_buf),
  .i2c2_scl_o(i2c2_scl_o),
  .uart1_tx_o_buf(uart1_tx_o_buf),
  .uart1_tx_o(uart1_tx_o),
  .uart1_rx_i_buf(uart1_rx_i_buf),
  .uart1_rx_i(uart1_rx_i),
  .uart2_tx_o_buf(uart2_tx_o_buf),
  .uart2_tx_o(uart2_tx_o),
  .uart2_rx_i_buf(uart2_rx_i_buf),
  .uart2_rx_i(uart2_rx_i),
  .gpio_a_i_buf(gpio_a_i_buf),
  .gpio_a_i(gpio_a_i),
  .gpio_a_o_buf(gpio_a_o_buf),
  .gpio_a_o(gpio_a_o),
  .gpio_a_t_buf(gpio_a_t_buf),
  .gpio_a_t(gpio_a_t)
);

adp_core adp_core0 (
  .adp_tck_i_buf(adp_tck_i_buf),
  .adp_trst_i_buf(adp_trst_sync),
  .adp_tms_i_buf(adp_tms_i_buf),
  .adp_tdi_i_buf(adp_tdi_i_buf),
  .adp_tdo_o_buf(adp_tdo_o_buf),
  .adp_tst_o_buf(adp_tst_o_buf),
  .adp_imem_stall(adp_imem_stall),
  .adp_dmem_stall(adp_dmem_stall),
  .adp_func_stall(adp_func_stall),
  .adp_load_hazard(adp_load_hazard),
  .adp_dmem_rdata(adp_dmem_rdata),
  .adp_core_reg(adp_core_reg),
  .adp_core_pc(adp_core_pc),
  .adp_core_ir(adp_core_ir),
  .adp_core_adc(adp_core_adc),
  .adp_core_dac(adp_core_dac),
  .adp_scan_end(adp_scan_end),
  .adp_bscan_end(adp_bscan_end),
  .adp_dmem_addr(adp_dmem_addr),
  .adp_dmem_rmask(adp_dmem_rmask),
  .adp_dmem_wmask(adp_dmem_wmask),
  .adp_dmem_wdata(adp_dmem_wdata),
  .adp_rd_addr(adp_rd_addr),
  .adp_wdata(adp_wdata),
  .adp_reg_we(adp_reg_we),
  .adp_pc_we(adp_pc_we),
  .adp_ir_we(adp_ir_we),
  .adp_adc_we(adp_adc_we),
  .adp_dac_we(adp_dac_we),
  .adp_ctrl_stall(adp_ctrl_stall),
  .adp_scan_enable(adp_scan_enable), // FIXME: Attach to Scan Chain
  .adp_scan_start(adp_scan_start),
  .adp_bscan_se(adp_bscan_se),
  .adp_bscan_oe(adp_bscan_oe),
  .adp_bscan_shift_sel(adp_bscan_shift_sel),
  .adp_bscan_out_sel(adp_bscan_out_sel),
  .adp_bscan_start(adp_bscan_start),
  .adp_debug_mode(adp_debug_mode)
);

// FIXME: Scan Chain Stubs
assign adp_scan_end = adp_scan_start;

////////////////////////////////////////////////////////////////////////////////
// Core Clock Domain
////////////////////////////////////////////////////////////////////////////////

// Glitch-free Clock Mux
acadia_clk_mux sys_clk_mux0 (
  .clk1(cpu_clk),
  .clk2(adp_tck_i_buf),
  .rst(sys_rst_sync),
  .sel(adp_debug_mode),
  .out_clk(cpu_main_clk)
);

cpu cpu0 (
  .clk(cpu_main_clk),
  .rst(cpu_rst_sync),

  .imem_addr(imem_addr),
  .imem_rmask(imem_rmask),
  .imem_rdata(imem_rdata),
  .imem_resp(imem_resp),

  .dmem_addr(dmem_addr),
  .dmem_rmask(dmem_rmask),
  .dmem_wmask(dmem_wmask),
  .dmem_rdata(dmem_rdata),
  .dmem_wdata(dmem_wdata),
  .dmem_resp(dmem_resp),

  .interrupt_serviced(interrupt_serviced),
  .interrupt_PC(interrupt_PC),
  .signal_interrupt(signal_interrupt),
  .int_accepted(int_accepted),


  .adp_core_reg(adp_core_reg),
  .adp_core_pc(adp_core_pc),
  .adp_core_ir(adp_core_ir),
  .adp_rd_addr(adp_rd_addr),
  .adp_wdata(adp_wdata),
  .adp_reg_we(adp_reg_we),
  .adp_pc_we(adp_pc_we),
  .adp_ir_we(adp_ir_we),
  .adp_imem_stall(adp_imem_stall),
  .adp_dmem_stall(adp_dmem_stall),
  .adp_func_stall(adp_func_stall),
  .adp_load_hazard(adp_load_hazard),
  .adp_ctrl_stall(adp_ctrl_stall)
);

icache #(
  .SETS(ICACHE_SETS),
  .CACHELINE(ICACHE_CACHELINE)
) icache0 (
  .clk(cpu_main_clk),
  .rst(cpu_rst_sync),

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

data_memory # (
  .NUM_WORDS(DMEM_WORDS),
  .WORDSIZE(DMEM_WORDSIZE)
) data_memory0 (
  .clk(cpu_main_clk),
  .rst(cpu_rst_sync),
  .dmem_addr(data_memory0_addr),
  .dmem_rmask(data_memory0_rmask),
  .dmem_wmask(data_memory0_wmask),
  .dmem_rdata(data_memory0_rdata),
  .dmem_wdata(data_memory0_wdata),
  .dmem_resp(data_memory0_resp)
);

mem_map_decoder  #(
  .INTERRUPT_LINES(NUM_INTERRUPTS)
) mem_map_decoder0(
  .clk(cpu_main_clk),
  .rst(cpu_rst_sync),

  .dmem_addr(dmem_addr),
  .dmem_rmask(dmem_rmask),
  .dmem_wmask(dmem_wmask),
  .dmem_rdata(dmem_rdata),
  .dmem_wdata(dmem_wdata),
  .dmem_resp(dmem_resp),

  /* DFP to Data SRAM */
  .data_memory0_addr(data_memory0_addr),
  .data_memory0_rmask(data_memory0_rmask),
  .data_memory0_wmask(data_memory0_wmask),
  .data_memory0_rdata(data_memory0_rdata),
  .data_memory0_wdata(data_memory0_wdata),
  .data_memory0_resp(data_memory0_resp),

  /* DFP to GPIO drivers */
  .gpio_a_addr(gpio_a_addr),
  .gpio_a_rmask(gpio_a_rmask),
  .gpio_a_wmask(gpio_a_wmask),
  .gpio_a_rdata(gpio_a_rdata),
  .gpio_a_wdata(gpio_a_wdata),
  .gpio_a_resp(gpio_a_resp),

  /* DFP to UART1 */
  .uart1_addr(uart1_addr),
  .uart1_rmask(uart1_rmask),
  .uart1_wmask(uart1_wmask),
  .uart1_rdata(uart1_rdata),
  .uart1_wdata(uart1_wdata),
  .uart1_resp(uart1_resp),

  /* DFP to UART2 */
  .uart2_addr(uart2_addr),
  .uart2_rmask(uart2_rmask),
  .uart2_wmask(uart2_wmask),
  .uart2_rdata(uart2_rdata),
  .uart2_wdata(uart2_wdata),
  .uart2_resp(uart2_resp),

  /* DFP to I2C1 controller */
  .i2c1_addr(i2c1_addr),
  .i2c1_rmask(i2c1_rmask),
  .i2c1_wmask(i2c1_wmask),
  .i2c1_rdata(i2c1_rdata),
  .i2c1_wdata(i2c1_wdata),
  .i2c1_resp(i2c1_resp),

  /* DFP to I2C2 controller */
  .i2c2_addr(i2c2_addr),
  .i2c2_rmask(i2c2_rmask),
  .i2c2_wmask(i2c2_wmask),
  .i2c2_rdata(i2c2_rdata),
  .i2c2_wdata(i2c2_wdata),
  .i2c2_resp(i2c2_resp),

  /* DFP to SPI controller */
  .spi1_addr(spi1_addr),
  .spi1_rmask(spi1_rmask),
  .spi1_wmask(spi1_wmask),
  .spi1_rdata(spi1_rdata),
  .spi1_wdata(spi1_wdata),
  .spi1_resp(spi1_resp),

  /* DFP to clock prescalers */
  .prescaler_rmask(prescaler_rmask),
  .prescaler_wmask(prescaler_wmask),
  .prescaler_rdata(prescaler_rdata),

  /* DFP to analog registers */
  .analog_addr(analog_addr),
  .analog_rmask(analog_rmask),
  .analog_wmask(analog_wmask),
  .analog_rdata(analog_rdata),
  .analog_wdata(analog_wdata),

  /*DFP to Interrupt Controller*/
  .intr_mask_val(int_mask_val),
  .read_int_mask(int_read_mask),
  .update_int_mask(update_int_mask),

  .int_vec_table_pc(int_vec_read_pc),
  .read_vec_table(read_vec_table),
  .update_int_vec_table(update_int_vec_table),
  .int_table_entry_id(table_entry_id),

  /*DFP to RSA */
  .RSA_output_msg(RSA_output_msg),
  .start_RSA(start_RSA),
  .RSA_idle_flag(RSA_idle),
  .update_key(update_key),
  .update_mod_n(update_mod_n),
  .update_msg_blk(update_msg_blk),

  .adp_dmem_rdata(adp_dmem_rdata),
  .adp_dmem_addr(adp_dmem_addr),
  .adp_dmem_rmask(adp_dmem_rmask),
  .adp_dmem_wmask(adp_dmem_wmask),
  .adp_dmem_wdata(adp_dmem_wdata),
  .adp_debug_mode(adp_debug_mode)
);

qspi_controller # (
  .DATA_NIBBLES(16)
) qspi_controller0 (
  .s_pclk(cpu_main_clk),
  .s_presetn(~cpu_rst_sync),
  .s_paddr(icache_addr),
  .s_psel(icache_read),
  .s_pwrite(1'b0),
  .s_pready(icache_resp),
  .s_prdata(icache_rdata),

  .qspi_io_i(qspi_io_i),
  .qspi_io_o(qspi_io_o),
  .qspi_io_t(qspi_io_t),
  .qspi_ck_o(qspi_ck_o),
  .qspi_cs_o(qspi_cs_o)
);

gpio # (
  .NUM_PINS(NUM_GPIO)
) gpio_controller_a (
  .clk(cpu_main_clk),
  .rst(cpu_rst_sync),

  .io_pins_in(gpio_a_i),
  .io_pins_out(gpio_a_o),
  .io_pins_tristate(gpio_a_t),

  .mem_addr(gpio_a_addr),
  .mem_rmask(gpio_a_rmask),
  .mem_wmask(gpio_a_wmask),
  .mem_rdata(gpio_a_rdata),
  .mem_wdata(gpio_a_wdata),
  .mem_resp(gpio_a_resp)
);



interrupt_controller #(
  .INTERRUPT_LINES(NUM_INTERRUPTS),
  .INTERRUPT_BITS($clog2(NUM_INTERRUPTS))
) interrupt_controller_a (
  .clk(cpu_main_clk), 
  .rst(cpu_rst_sync),

  .interrupt_id(interrupt_pins), 
  .in_service(in_service),

  .read_mask(int_read_mask), 
  .update_int_mask(update_int_mask),
  .wdata_int_mask(dmem_wdata[NUM_INTERRUPTS-1:0]),
  .int_mask_val(int_mask_val),

  .read_vec_table(read_vec_table),
  .table_entry_id(table_entry_id),
  .wdata_vec_table(dmem_wdata),
  .update_int_vec_table(update_int_vec_table),
  .int_vec_table_pc(int_vec_read_pc),

  .interrupt_serviced(interrupt_serviced),
  .interrupt_PC(interrupt_PC),
  .signal_interrupt(signal_interrupt),
  .int_accepted(int_accepted)
);

RSA_ACCELERATOR # (
  .KEY_SIZE_BITS(KEY_SIZE_LEN)
) rsa_accelerator_a (
  .clk(cpu_main_clk),
  .rst_n(~cpu_rst_sync),

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

uart_peripheral # (
  .RX_BUFFER_DEPTH(64),
  .TX_BUFFER_DEPTH(64),
  .D_BAUD_FREQ(12'd48),
  .D_BAUD_LIMIT(16'd3077)
) uart1 (
  .clk(cpu_main_clk),
  .rst(cpu_rst_sync),

  .int_req(uart1_int_req),

  .rx(uart1_rx_i),
  .tx(uart1_tx_o),

  .mem_addr(uart1_addr),
  .mem_rmask(uart1_rmask),
  .mem_wmask(uart1_wmask),
  .mem_rdata(uart1_rdata),
  .mem_wdata(uart1_wdata),
  .mem_resp(uart1_resp)
);

uart_peripheral # (
  .RX_BUFFER_DEPTH(64),
  .TX_BUFFER_DEPTH(64),
  .D_BAUD_FREQ(12'd48),
  .D_BAUD_LIMIT(16'd3077)
) uart2 (
  .clk(cpu_main_clk),
  .rst(cpu_rst_sync),

  .int_req(uart2_int_req),

  .rx(uart2_rx_i),
  .tx(uart2_tx_o),

  .mem_addr(uart2_addr),
  .mem_rmask(uart2_rmask),
  .mem_wmask(uart2_wmask),
  .mem_rdata(uart2_rdata),
  .mem_wdata(uart2_wdata),
  .mem_resp(uart2_resp)
);

assign i2c1_sda_t = ~SDA1;
assign i2c2_sda_t = ~SDA2;
assign i2c1_sda_o = '0;
assign i2c2_sda_o = '0;

i2c_peripheral # (
  .D_BAUD_FREQ(12'd1),
  .D_BAUD_LIMIT(16'd625)
) i2c1 (
  .clk(cpu_main_clk),
  .rst(cpu_rst_sync),

  .int_req(i2c1_int_req),

  .SDA_in(i2c1_sda_i),
  .SDA(SDA1), // TODO fix this, connect to IO cell
  .SCL(i2c1_scl_o),

  .mem_addr(i2c1_addr),
  .mem_rmask(i2c1_rmask),
  .mem_wmask(i2c1_wmask),
  .mem_rdata(i2c1_rdata),
  .mem_wdata(i2c1_wdata),
  .mem_resp(i2c1_resp)
);

i2c_peripheral # (
  .D_BAUD_FREQ(12'd1),
  .D_BAUD_LIMIT(16'd625)
) i2c2 (
  .clk(cpu_main_clk),
  .rst(cpu_rst_sync),

  .int_req(i2c2_int_req),

  .SDA_in(i2c2_sda_i),
  .SDA(SDA2), // TODO fix this, connect to IO cell
  .SCL(i2c2_scl_o),

  .mem_addr(i2c2_addr),
  .mem_rmask(i2c2_rmask),
  .mem_wmask(i2c2_wmask),
  .mem_rdata(i2c2_rdata),
  .mem_wdata(i2c2_wdata),
  .mem_resp(i2c2_resp)
);

spi_peripheral # (

) spi1 (
  .clk(cpu_main_clk),
  .rst(cpu_rst_sync),

  .MOSI(spi_mosi_o),
  .SCLK(spi_sclk_o),

  .mem_addr(spi1_addr),
  .mem_rmask(spi1_rmask),
  .mem_wmask(spi1_wmask),
  .mem_rdata(spi1_rdata),
  .mem_wdata(spi1_wdata),
  .mem_resp(spi1_resp)
);

analog_ctrl analog_ctrl0 (
  .clk(cpu_main_clk),
  .rst(cpu_rst_sync),
  .analog_clk(adc_clk),
  .analog_rst(adc_rst_sync),
  .dmem_addr(analog_addr),
  .dmem_rmask(analog_rmask),
  .dmem_wmask(analog_wmask),
  .dmem_wdata(analog_wdata),
  .analog_rdata(analog_rdata),
  .adp_core_adc(adp_core_adc),
  .adp_core_dac(adp_core_dac),
  .adp_wdata(adp_wdata),
  .adp_adc_we(adp_adc_we),
  .adp_dac_we(adp_dac_we),
  .adc_eoc_n(adc_eoc_n),
  .adc_data(adc_data),
  .adc_firmware_en(adc_firmware_en),
  .adc_adc_en(adc_adc_en),
  .adc_calib_en(adc_calib_en),
  .adc_eoc_2ff(adc_eoc_2ff),
  .adc_ext_opt(adc_ext_opt),
  .dac_reg_slow(dac_reg),
  .dac_ack(dac_interrupt)
);

////////////////////////////////////////////////////////////////////////////////
// Peripheral Clock Domain
////////////////////////////////////////////////////////////////////////////////

endmodule : core
