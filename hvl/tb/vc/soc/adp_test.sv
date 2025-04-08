module run_adp_test
import adp_types::*;
(
  adp_itf adp_if,
  output bit test_halt
);

localparam START_DELAY_LOW  = 10;
localparam START_DELAY_HIGH = 1000;

integer start_delay;

/* ADP Clock Generation */
int adp_clock_half_period_ns = 10;

bit tck, tck_en;
initial begin
  tck <= 0; // #0 nonblocking assignment ~ negedge clock event
  forever #(adp_clock_half_period_ns) tck = ~tck;
end

/* Control Test Clock w/ Enable driven by Testbench */
assign adp_if.tck = tck & tck_en;

/**
 * Enable ADP interface TCK
 */
task enable_tck();
  @(negedge tck);
  tck_en <= 1'b1;
endtask

/**
 * Disable ADP interface TCK
 */
task disable_tck();
  @(negedge tck);
  tck_en <= 1'b0;
endtask

initial begin
  // Wait for random delay to simulate using ADP during processor workload
  std::randomize(start_delay) with {
    start_delay inside {[START_DELAY_LOW:START_DELAY_HIGH]};
  };
  repeat(start_delay) @(negedge tck);

  $display();
  $display("==================");
  $display("Starting ADP Test!");
  $display("==================");
  $display();

  start_test();

  adp_bringup_test();
  adp_scan_mode_test();
  adp_boundary_scan_test();
  adp_bypass_mode_test();
  adp_debug_read_write_test();
  adp_step_mode_test();

  end_test();

  $display();
  $display("==================");
  $display("Ending ADP Test!");
  $display("==================");
  $display();

end

/**
 * Enable test clock, set TAP to IDLE, then set TAP to PAUSE
 */
task start_test();
  enable_tck();
  adp_if.initialize();
  adp_if.idle();
  adp_if.pause();
endtask : start_test

/**
 * adp_bringup_test();
 * The most basic bringup for ADP is reading the IDCODE register, 
 * which contains Acadia's DEVICE ID, 0x69ECE498.
 *
 * This is the most basic way to check the ADP is working.
 */
task adp_bringup_test();
  logic [31:0] device_id;

  // Set Instruction Register to DEVICE_ID_READ
  adp_if.ir_write({4'b0000, DEVICE_ID_READ});

  // Read DEVICE ID from Scan Register
  adp_if.sr_read(device_id);

  check_device_id : assert(device_id == ACADIA_DEVICE_ID) begin
    $display("[adp_bringup_test] [PASS] Device ID %0H read successfully", device_id);
  end
  else begin
    $display("[adp_bringup_test] [ERROR] Device ID %0H read incorrectly", device_id);
  end
endtask : adp_bringup_test

/**
 * adp_scan_mode_test();
 * Make sure there are no stuck at conditions.
 *
 * When inserting all 1s, the shift out data on TDO should never be 0s. 
 * This is the stuck-at 0 check.
 *
 * When inserting all 0s, the shift out data on TDO should never be 1s. 
 * This is the stuck-at 1 check.
 */
task adp_scan_mode_test();
  integer scan_chain_length = 1000;

  // Set Instruction Register to SCAN_MODE
  adp_if.ir_write({4'b0000, SCAN_MODE});

  // Insert all 1s into scan chain, and check for stuck-at 0s
  adp_if.scan_stuck_0_test(scan_chain_length);

  // Insert all 0s into scan chain, and check for stuck-at 1s
  adp_if.scan_stuck_1_test(scan_chain_length);

  // Report no assertion errors
  $display("[adp_scan_mode_test] [PASS] Tests Passed Successfully!");

endtask : adp_scan_mode_test

/**
 * adp_boundary_scan_test();
 * Check that boundary scan shifting works as expected.
 *
 * Make sure that we can shift in to each boundary scan cell without losing
 * the data in the test vector. 
 *
 * Conduct a capture test where we sample the input data from each pin,
 * then shift the data vector out.
 *
 * Conduct a output test where we shift the input data, then update the each
 * pin with the new test vector.  
 */
task adp_boundary_scan_test();

  // Set Instruction Register to BOUNDARY_SCAN
  adp_if.ir_write({4'b0000, BOUNDARY_SCAN});

  // Check boundary scan cells are all accessable
  adp_itf.boundary_scan_shift_test();

  // Check boundary scan cells can capture data
  adp_itf.boundary_scan_capture_test();

  // Check boundary scan cells can update data
  adp_itf.boundary_scan_update_test();

  // Report no assertion errors
  $display("[adp_boundary_scan_test] [PASS] Tests Passed Successfully!");

endtask : adp_boundary_scan_test

/**
 * adp_bypass_mode_test();
 * Check that the data shifted in on TDI is shifted out on TDO with 1 cycle of
 * latency.
 */
task adp_bypass_mode_test();
  logic [31:0] bypass_vector;

  // Set Instruction Register to BYPASS_MODE
  adp_if.ir_write({4'b0000, BYPASS_MODE});

  // Test Bypass Register
  repeat(10) begin
    fork
      begin
        // Write bypass test vector
        std::randomize(bypass_vector);
        adp_if.sr_write(bypass_vector);
      end

      begin
        // Wait for bypass output
        repeat(4) @(adp_if.cb);
        for (int i = 31; i > 0; i--) begin
          check_bypass_reg : assert(adp_if.cb.tdo == bypass_vector[i]) 
          else begin
            $display("[check_bypass_reg] [ERROR] Bypass value read incorrectly: %0d, %0d", adp_if.cb.tdo, bypass_vector[i]);
          end
          @(adp_if.cb);
        end
      end
    join
    $display("[adp_bypass_mode_test] [PASS] Bypass Vector %0H read successfully", bypass_vector);
  end
endtask : adp_bypass_mode_test

/**
 * adp_debug_read_write_test();
 * Check that we can read and write to and from the given ADP address map.
 *
 * Write and Read to all SRAM locations.
 * Write and Read to all processor registers.
 * Write and Read to processor program counter.
 * Write and Read to processor instruction register.
 */
task adp_debug_read_write_test();
  bit [31:0] rand_data;
  bit [31:0] actual_data;
  bit [SRAM_ADDR_WIDTH-1:0] sram_offset;
  bit [4:0] reg_offset;

  //////////////////////////////////////////////////////////////////////////////
  // Test SRAM
  //////////////////////////////////////////////////////////////////////////////

  // Read and write to all SRAM locations.
  for (int i = 0; i < 2**SRAM_ADDR_WIDTH; i++) begin
    // Set Instruction Register to DEBUG_WRITE
    adp_if.ir_write({4'b0000, DEBUG_WRITE});

    // Set SRAM address
    adp_if.ar_write({3'b001, sram_offset});
    sram_offset++;

    // Write to SRAM location
    std::randomize(rand_data);
    adp_if.dr_write(rand_data);

    // Set Instruction Register to DEBUG_READ
    adp_if.ir_write({4'b0000, DEBUG_READ});

    // Read from SRAM location
    adp_if.dr_read(actual_data);

    check_sram_rw : assert (actual_data == rand_data)
    else begin
      $display("[check_sram_rw] [ERROR] Read %0H mismatch %0H", actual_data, rand_data);
    end
  end

  // Report no assertion errors
  $display("[check_sram_rw] [PASS] All SRAM Locations Tested Successfully!");

  //////////////////////////////////////////////////////////////////////////////
  // Test Registers
  //////////////////////////////////////////////////////////////////////////////

  // Read and write to all processor registers.
  for (int i = 0; i < 31; i++) begin
    // Set Instruction Register to DEBUG_WRITE
    adp_if.ir_write({4'b0000, DEBUG_WRITE});

    // Set REG address
    adp_if.ar_write({11'b01000000000, reg_offset + 1'b1}); // +1 to avoid x0
    reg_offset++;

    // Write to REG location
    std::randomize(rand_data);
    adp_if.dr_write(rand_data);

    // Set Instruction Register to DEBUG_READ
    adp_if.ir_write({4'b0000, DEBUG_READ});

    // Read from REG location
    adp_if.dr_read(actual_data);

    check_reg_rw : assert (actual_data == rand_data)
    else begin
      $display("[check_reg_rw] [ERROR] Read %0H mismatch %0H", actual_data, rand_data);
    end
  end

  // Report no assertion errors
  $display("[check_reg_rw] [PASS] All REG Locations Tested Successfully!");

  //////////////////////////////////////////////////////////////////////////////
  // Test Program Counter and Instruction Register
  //////////////////////////////////////////////////////////////////////////////

  // Read and write to processor program counter.
  // Set Instruction Register to DEBUG_WRITE
  adp_if.ir_write({4'b0000, DEBUG_WRITE});

  // Set Program Counter Address
  adp_if.ar_write(16'h8000);

  // Write to Program Counter location
  std::randomize(rand_data);
  adp_if.dr_write(rand_data);

  // Set Instruction Register to DEBUG_READ
  adp_if.ir_write({4'b0000, DEBUG_READ});

  // Read from Program Counter location
  adp_if.dr_read(actual_data);

  check_pc_rw : assert (actual_data == rand_data)
  else begin
    $display("[check_pc_rw] [ERROR] Read %0H mismatch %0H", actual_data, rand_data);
  end

  // Report no assertion errors
  $display("[check_pc_rw] [PASS] Program Counter Tested Successfully!");

  // Read and write to processor instruction register.
  // Set Instruction Register to DEBUG_WRITE
  adp_if.ir_write({4'b0000, DEBUG_WRITE});

  // Set Instruction Register address
  adp_if.ar_write(16'h8001);

  // Write to Instruction Register location
  std::randomize(rand_data);
  adp_if.dr_write(rand_data);

  // Set Instruction Register to DEBUG_READ
  adp_if.ir_write({4'b0000, DEBUG_READ});

  // Read from Instruction Register location
  adp_if.dr_read(actual_data);

  check_ir_rw : assert (actual_data == rand_data)
  else begin
    $display("[check_ir_rw] [ERROR] Read %0H mismatch %0H", actual_data, rand_data);
  end

  // Report no assertion errors
  $display("[check_ir_rw] [PASS] Instruction Register Tested Successfully!");

  //////////////////////////////////////////////////////////////////////////////
  // Test ADC and DAC Registers
  //////////////////////////////////////////////////////////////////////////////

  // Read and write to processor program counter.
  // Set Instruction Register to DEBUG_WRITE
  adp_if.ir_write({4'b0000, DEBUG_WRITE});

  // Set Program Counter Address
  adp_if.ar_write(16'h8002);

  // Write to Program Counter location
  std::randomize(rand_data);
  adp_if.dr_write(rand_data);

  // Set Instruction Register to DEBUG_READ
  adp_if.ir_write({4'b0000, DEBUG_READ});

  // Read from Program Counter location
  adp_if.dr_read(actual_data);

  check_adc_rw : assert ((actual_data & 'hFF00) == (rand_data & 'hFF00))
  else begin
    $display("[check_adc_rw] [ERROR] Read %0H mismatch %0H", (actual_data & 'hFF00), (rand_data & 'hFF00));
  end

  // Report no assertion errors
  $display("[check_adc_rw] [PASS] Program Counter Tested Successfully!");

  // Read and write to processor instruction register.
  // Set Instruction Register to DEBUG_WRITE
  adp_if.ir_write({4'b0000, DEBUG_WRITE});

  // Set Instruction Register address
  adp_if.ar_write(16'h8003);

  // Write to Instruction Register location
  std::randomize(rand_data);
  adp_if.dr_write(rand_data);

  // Set Instruction Register to DEBUG_READ
  adp_if.ir_write({4'b0000, DEBUG_READ});

  // Read from Instruction Register location
  adp_if.dr_read(actual_data);

  check_dac_rw : assert ((actual_data & 'h00FF) == (rand_data & 'h00FF))
  else begin
    $display("[check_dac_rw] [ERROR] Read %0H mismatch %0H", (actual_data & 'h00FF), (rand_data & 'h00FF));
  end

  // Report no assertion errors
  $display("[check_dac_rw] [PASS] Instruction Register Tested Successfully!");

  // Report no assertion errors
  $display("[adp_debug_read_write_test] [PASS] Tests Passed Successfully!");

endtask : adp_debug_read_write_test

/**
 * adp_step_mode_test();
 * Check that we can stall the processor using TDI as step mode.
 */
task adp_step_mode_test();

  // Set Instruction Register to STEP_MODE
  adp_if.ir_write({4'b0000, STEP_MODE});

  // Check stalls
  adp_if.step_mode_stall_test();

  // Report no assertion errors
  $display("[adp_step_mode_test] [PASS] Tests Passed Successfully!");

endtask : adp_step_mode_test

/**
 * End test by asserting test_halt high
 */
task end_test();
  adp_if.idle();
  test_halt = 1'b1;
endtask : end_test

endmodule : run_adp_test