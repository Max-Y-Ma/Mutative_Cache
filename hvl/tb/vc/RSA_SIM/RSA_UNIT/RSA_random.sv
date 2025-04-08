//-----------------------------------------------------------------------------
// Title         : RSA_random.svh
// Project       : Acadia 
//-----------------------------------------------------------------------------
// File          : RSA_random.svh
// Author        : Shiv Gohil
//-----------------------------------------------------------------------------
module RSA_random_top_tb
(
    input logic clk,
    input logic rst_n,
    output logic error_flag
);


  `include "RSA_randinst.svh"
  RandInst gen = new();

  task init_register_state();
      gen.randomize();
      itf.key       <= gen.instr.word;
      itf.mod_n     <= gen.instr.word;
      itf.msg_block <= gen.instr.word;
      itf.start <= 1'b1;
  endtask : init_register_state

  //Run task to test RSA_accelerator with random inputs/use assertions to compare outputs
  task run_random_inputs();
    repeat (5000) begin
      @(posedge clk);

      // Always read out a valid instruction.
      if (itf.complete_flag) begin
        gen.randomize();
        itf.rdata <= gen.instr.word;
      end

      // If it's a write, do nothing and just respond.
      itf.resp <= 1'b1;
      @(posedge itf.clk) itf.resp <= 1'b0;
    end
  endtask : run_random_inputs

  // A single initial block ensures random stability.
  initial begin

    // Wait for reset.
    @(posedge clk iff rst_n == 1'b1);


    // Run!
    run_random_inputs();

    // Finish up
    $display("Random testbench finished!");
    $finish;
  end

endmodule : RSA_random_top_tb
