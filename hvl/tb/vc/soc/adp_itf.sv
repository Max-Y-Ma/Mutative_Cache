interface adp_itf;

import adp_types::*;

logic       tck;
logic       tms;
logic       tdi;
logic       tdo;
logic [3:0] tst;

clocking cb @(negedge tck);
  input tdo, tst;
  output tms, tdi;
endclocking

/**
 * This task drives TAP state machine using TMS
 */
task drive_tap(input logic value);
  cb.tms <= value;
  @(cb);
endtask : drive_tap

/**
 * This task is responsible for initializing the interface signals.
 */
task initialize();
  tms <= 1'b0;
  tdi <= 1'b0;
endtask : initialize

/**
 * Set TAP to Idle State, which must be done to initialize 
 * control over the ADP. The TAP is garunteed to be in IDLE after size cycles
 * with TMS driven high.
 */
task idle();
  // Wait RESET_CYCLE number of cycles
  repeat(RESET_CYCLES) begin
    drive_tap(1'b1);
  end
  
  // Check TAP State
  check_idle : assert(cb.tst == IDLE) begin
    $display("[check_idle] [PASS] Correctly set TAP to IDLE");
  end
  else begin
    $display("[check_idle] [ERROR] Did not set TAP to IDLE");
  end
endtask : idle

/**
 * Set TAP to Pause State, which must be called before executing any 
 * instructions on the ADP. This is typically called after the idle function.
 */
task pause();
  drive_tap(1'b0); // DR_SCAN
  drive_tap(1'b1); // SR_SCAN
  drive_tap(1'b0); // SR_SHIFT
  drive_tap(1'b1); // PAUSE

  check_pause : assert(cb.tst == PAUSE) begin
    $display("[check_pause] [PASS] Correctly set TAP to PAUSE");
  end
  else begin
    $display("[check_pause] [ERROR] Did not set TAP to PAUSE, actual state %0d", cb.tst);
  end
endtask : pause

/**
 * Tasks after this point assume the TAP is already in PAUSE
 */

/**
 * Data Regsiter Read:
 * Set TAP to DR_SCAN -> DR_JUMP -> DR_SETUP -> IN_CAPTURE -> IN_SHIFT -> PAUSE.
 * This will shift the data register out onto TDO which will be returned.
 */
task dr_read(output logic [31:0] data_reg);
  drive_tap(1'b1); // DR_SCAN
  drive_tap(1'b0); // DR_JUMP
  drive_tap(1'b1); // DR_SETUP
  drive_tap(1'b0); // IN_CAPTURE
  drive_tap(1'b0); // IN_SHIFT

  repeat(31) begin
    data_reg <= {data_reg[30:0], cb.tdo};
    drive_tap(1'b0); // IN_SHIFT
  end
  
  data_reg <= {data_reg[30:0], cb.tdo};
  drive_tap(1'b1); // PAUSE

  dr_read_check_pause : assert(cb.tst == PAUSE)
  else begin
    $display("[dr_read_check_pause] [ERROR] Did not set TAP to PAUSE, actual state %0d", cb.tst);
  end
endtask : dr_read

/**
 * Data Register Write:
 * Set TAP to DR_SCAN -> DR_JUMP -> EX_SHIFT -> EX_UPDATE -> PAUSE. This will
 * shift in the provided data argument to the data register using TDO.
 */
task dr_write(input logic [31:0] data_reg);
  drive_tap(1'b1); // DR_SCAN
  drive_tap(1'b0); // DR_JUMP
  drive_tap(1'b0); // EX_SHIFT

  repeat(31) begin
    cb.tdi <= data_reg[31];
    data_reg <= {data_reg[30:0], data_reg[31]};
    drive_tap(1'b0); // EX_SHIFT
  end

  cb.tdi <= data_reg[31];
  data_reg <= {data_reg[30:0], data_reg[31]};
  drive_tap(1'b1); // EX_UPDATE

  drive_tap(1'b1); // PAUSE

  dr_write_check_pause : assert(cb.tst == PAUSE)
  else begin
    $display("[dr_write_check_pause] [ERROR] Did not set TAP to PAUSE, actual state %0d", cb.tst);
  end
endtask : dr_write

/**
 * Scan Register Read:
 * Set TAP to DR_SCAN -> SR_SCAN -> SR_SHIFT -> PAUSE. This will shift the 
 * scan register out onto TDO which will be returned.
 */
task sr_read(output logic [31:0] scan_reg);
  drive_tap(1'b1); // DR_SCAN
  drive_tap(1'b1); // SR_SCAN
  drive_tap(1'b0); // SR_SHIFT

  repeat(31) begin
    scan_reg <= {scan_reg[30:0], cb.tdo};
    drive_tap(1'b0); // SR_SHIFT
  end
  
  scan_reg <= {scan_reg[30:0], cb.tdo};
  drive_tap(1'b1); // PAUSE

  sr_read_check_pause : assert(cb.tst == PAUSE)
  else begin
    $display("[sr_read_check_pause] [ERROR] Did not set TAP to PAUSE, actual state %0d", cb.tst);
  end
endtask : sr_read

/**
 * Scan Register Write:
 * Set TAP to DR_SCAN -> SR_SCAN -> SR_SHIFT -> PAUSE. This will shift in the
 * provided data argument to the scan register using TDO.
 */
task sr_write(input logic [31:0] scan_reg);
  drive_tap(1'b1); // DR_SCAN
  drive_tap(1'b1); // SR_SCAN
  drive_tap(1'b0); // SR_SHIFT

  repeat(31) begin
    cb.tdi <= scan_reg[31];
    scan_reg <= {scan_reg[30:0], scan_reg[31]};
    drive_tap(1'b0); // SR_SHIFT
  end

  cb.tdi <= scan_reg[31];
  scan_reg <= {scan_reg[30:0], scan_reg[31]};
  drive_tap(1'b1); // PAUSE

  sr_write_check_pause : assert(cb.tst == PAUSE)
  else begin
    $display("[sr_write_check_pause] [ERROR] Did not set TAP to PAUSE, actual state %0d", cb.tst);
  end
endtask : sr_write

/**
 * Instruction Register Read:
 * Set TAP to DR_SCAN -> SR_SCAN -> IR_SCAN -> IR_CAPTURE -> IR_SHIFT -> PAUSE. 
 * This will shift the instruction register out onto TDO which will be returned.
 */
task ir_read(output logic [6:0] inst_reg);
  drive_tap(1'b1); // DR_SCAN
  drive_tap(1'b1); // SR_SCAN
  drive_tap(1'b1); // IR_SCAN
  drive_tap(1'b0); // IR_CAPTURE
  drive_tap(1'b0); // IR_SHIFT

  repeat(6) begin
    inst_reg <= {inst_reg[5:0], cb.tdo};
    drive_tap(1'b0); // IR_SHIFT
  end
  
  inst_reg <= {inst_reg[5:0], cb.tdo};
  drive_tap(1'b1); // PAUSE

  ir_read_check_pause : assert(cb.tst == PAUSE)
  else begin
    $display("[ir_read_check_pause] [ERROR] Did not set TAP to PAUSE, actual state %0d", cb.tst);
  end
endtask : ir_read

/**
 * Instruction Register Write:
 * Set TAP to DR_SCAN -> SR_SCAN -> IR_SCAN -> IR_CAPTURE -> IR_SHIFT -> PAUSE. 
 * This will shift in the provided data argument to the instruction register using TDO.
 */
task ir_write(input logic [6:0] inst_reg);
  drive_tap(1'b1); // DR_SCAN
  drive_tap(1'b1); // SR_SCAN
  drive_tap(1'b1); // IR_SCAN
  drive_tap(1'b0); // IR_CAPTURE
  drive_tap(1'b0); // IR_SHIFT

  repeat(6) begin
    cb.tdi <= inst_reg[6];
    inst_reg <= {inst_reg[5:0], inst_reg[6]};
    drive_tap(1'b0); // IR_SHIFT
  end

  cb.tdi <= inst_reg[6];
  inst_reg <= {inst_reg[5:0], inst_reg[6]};
  drive_tap(1'b1); // PAUSE

  ir_write_check_pause : assert(cb.tst == PAUSE)
  else begin
    $display("[ir_write_check_pause] [ERROR] Did not set TAP to PAUSE, actual state %0d", cb.tst);
  end
endtask : ir_write

/**
 * Address Register Read:
 * Set TAP to DR_SCAN -> SR_SCAN -> IR_SCAN -> AR_SCAN -> AR_SHIFT -> PAUSE. 
 * This will shift the address register out onto TDO which will be returned.
 */
task ar_read(output logic [31:0] addr_reg);
  drive_tap(1'b1); // DR_SCAN
  drive_tap(1'b1); // SR_SCAN
  drive_tap(1'b1); // IR_SCAN
  drive_tap(1'b1); // AR_SCAN
  drive_tap(1'b0); // AR_SHIFT

  repeat(31) begin
    addr_reg <= {addr_reg[30:0], cb.tdo};
    drive_tap(1'b0); // AR_SHIFT
  end
  
  addr_reg <= {addr_reg[30:0], cb.tdo};
  drive_tap(1'b1); // PAUSE

  ar_read_check_pause : assert(cb.tst == PAUSE)
  else begin
    $display("[ar_read_check_pause] [ERROR] Did not set TAP to PAUSE, actual state %0d", cb.tst);
  end
endtask : ar_read

/**
 * Address Register Write:
 * Set TAP to DR_SCAN -> SR_SCAN -> IR_SCAN -> AR_SCAN -> AR_SHIFT -> PAUSE. 
 * This will shift in the provided data argument to the address register using TDO.
 */
task ar_write(input logic [31:0] addr_reg);
  drive_tap(1'b1); // DR_SCAN
  drive_tap(1'b1); // SR_SCAN
  drive_tap(1'b1); // IR_SCAN
  drive_tap(1'b1); // AR_SCAN
  drive_tap(1'b0); // AR_SHIFT

  repeat(31) begin
    cb.tdi <= addr_reg[31];
    addr_reg <= {addr_reg[30:0], addr_reg[31]};
    drive_tap(1'b0); // AR_SHIFT
  end

  cb.tdi <= addr_reg[31];
  addr_reg <= {addr_reg[30:0], addr_reg[31]};
  drive_tap(1'b1); // PAUSE

  ar_write_check_pause : assert(cb.tst == PAUSE)
  else begin
    $display("[ar_write_check_pause] [ERROR] Did not set TAP to PAUSE, actual state %0d", cb.tst);
  end
endtask : ar_write

/**
 * Scan Chain Stuck-At 0 Test
 */
task scan_stuck_0_test(input integer scan_chain_length);
  drive_tap(1'b1); // DR_SCAN
  drive_tap(1'b1); // SR_SCAN
  drive_tap(1'b0); // SR_SHIFT

  // Insert all 1s into scan chain
  repeat(scan_chain_length) begin
    cb.tdi <= 1'b1;
    drive_tap(1'b0); // SR_SHIFT
  end

  // Check for stuck-at 0s
  repeat(scan_chain_length) begin
    scan_stuck_0_check_tdo : assert(cb.tdo == 1'b1) 
    else begin
      $display("[scan_stuck_0_check_tdo] [ERROR] Stuck-At 0 Failed, TDO contains %0d", cb.tdo);
    end

    cb.tdi <= 1'b1;
    drive_tap(1'b0); // SR_SHIFT
  end

  drive_tap(1'b1); // PAUSE

  scan_stuck_0_check_pause : assert(cb.tst == PAUSE)
  else begin
    $display("[scan_stuck_0_check_pause] [ERROR] Did not set TAP to PAUSE, actual state %0d", cb.tst);
  end
endtask : scan_stuck_0_test

/**
 * Scan Chain Stuck-At 1 Test
 */
task scan_stuck_1_test(input integer scan_chain_length);
  drive_tap(1'b1); // DR_SCAN
  drive_tap(1'b1); // SR_SCAN
  drive_tap(1'b0); // SR_SHIFT

  // Insert all 1s into scan chain
  repeat(scan_chain_length) begin
    cb.tdi <= 1'b0;
    drive_tap(1'b0); // SR_SHIFT
  end

  // Check for stuck-at 1s
  repeat(scan_chain_length) begin
    scan_stuck_1_check_tdo : assert(cb.tdo == 1'b0) 
    else begin
      $display("[scan_stuck_1_check_tdo] [ERROR] Stuck-At 1 Failed, TDO contains %0d", cb.tdo);
    end

    cb.tdi <= 1'b0;
    drive_tap(1'b0); // SR_SHIFT
  end

  drive_tap(1'b1); // PAUSE

  scan_stuck_1_check_pause : assert(cb.tst == PAUSE)
  else begin
    $display("[scan_stuck_1_check_pause] [ERROR] Did not set TAP to PAUSE, actual state %0d", cb.tst);
  end
endtask : scan_stuck_1_test

/**
 * Make sure that we can shift in to each boundary scan cell without losing
 * the data in the test vector. 
 */
task boundary_scan_shift_test();
  logic [NUM_BOUNDARY_CELLS-1:0] test_vector;

  drive_tap(1'b1); // DR_SCAN
  drive_tap(1'b0); // DR_JUMP
  drive_tap(1'b0); // EX_SHIFT

  repeat(10) begin
    std::randomize(test_vector);
    repeat(NUM_BOUNDARY_CELLS) begin
      test_vector <= {test_vector[NUM_BOUNDARY_CELLS-2:0], test_vector[NUM_BOUNDARY_CELLS-1]};
      cb.tdi <= test_vector[NUM_BOUNDARY_CELLS-1];
      drive_tap(1'b0); // EX_SHIFT
    end

    repeat(NUM_BOUNDARY_CELLS) begin
      boundary_scan_shift_check_tdo : assert(cb.tdo == test_vector[NUM_BOUNDARY_CELLS-1]) 
      else begin
        $display("[boundary_scan_shift_check_tdo] [ERROR] Boundary Scan Shift Failed, %0d vs %0d", cb.tdo, test_vector[NUM_BOUNDARY_CELLS-1]);
      end

      test_vector <= {test_vector[NUM_BOUNDARY_CELLS-2:0], cb.tdo};
      drive_tap(1'b0); // EX_SHIFT
    end
    
    $display("[boundary_scan_shift_test] [PASS] Correctly shifted in %0H", test_vector);
  end

  drive_tap(1'b1); // EX_UPDATE
  drive_tap(1'b1); // PAUSE

  boundary_scan_shift_check_pause : assert(cb.tst == PAUSE)
  else begin
    $display("[boundary_scan_shift_check_pause] [ERROR] Did not set TAP to PAUSE, actual state %0d", cb.tst);
  end

endtask : boundary_scan_shift_test

/**
 * Conduct a capture test where we sample the input data from each pin,
 * then shift the data vector out.
 */
task boundary_scan_capture_test();
  drive_tap(1'b1); // DR_SCAN
  drive_tap(1'b0); // DR_JUMP
  drive_tap(1'b1); // DR_SETUP
  drive_tap(1'b0); // IN_CAPTURE
  drive_tap(1'b0); // IN_SHIFT

  repeat(NUM_BOUNDARY_CELLS-1) begin
    drive_tap(1'b0); // IN_SHIFT
  end
  
  drive_tap(1'b1); // PAUSE

  boundary_scan_capture_check_pause : assert(cb.tst == PAUSE)
  else begin
    $display("[boundary_scan_capture_check_pause] [ERROR] Did not set TAP to PAUSE, actual state %0d", cb.tst);
  end

endtask : boundary_scan_capture_test

/**
 * Conduct a output test where we shift the input data, then update each
 * pin with the new test vector.
 */
task boundary_scan_update_test();
  bit shift_bit;

  drive_tap(1'b1); // DR_SCAN
  drive_tap(1'b0); // DR_JUMP
  drive_tap(1'b0); // EX_SHIFT

  repeat(NUM_BOUNDARY_CELLS-1) begin
    std::randomize(shift_bit);
    cb.tdi <= shift_bit;
    drive_tap(1'b0); // EX_SHIFT
  end

  std::randomize(shift_bit);
  cb.tdi <= shift_bit;
  drive_tap(1'b1); // EX_UPDATE

  drive_tap(1'b1); // PAUSE

  boundary_scan_update_check_pause : assert(cb.tst == PAUSE)
  else begin
    $display("[boundary_scan_update_check_pause] [ERROR] Did not set TAP to PAUSE, actual state %0d", cb.tst);
  end

endtask : boundary_scan_update_test

/**
 * Check that we can stall the processor using TDI as step mode.
 */
task step_mode_stall_test();
  bit stall_bit;

  drive_tap(1'b1); // DR_SCAN
  drive_tap(1'b1); // SR_SCAN
  drive_tap(1'b0); // SR_SHIFT

  repeat(10) begin
    std::randomize(stall_bit);
    cb.tdi <= stall_bit;
    drive_tap(1'b0); // SR_SHIFT
  end

  std::randomize(stall_bit);
  cb.tdi <= stall_bit;  
  drive_tap(1'b1); // PAUSE

  step_mode_stall_check_pause : assert(cb.tst == PAUSE)
  else begin
    $display("[step_mode_stall_check_pause] [ERROR] Did not set TAP to PAUSE, actual state %0d", cb.tst);
  end


endtask : step_mode_stall_test

endinterface
