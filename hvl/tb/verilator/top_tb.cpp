#include <queue>
#include <time.h>
#include <string>
#include <fstream>
#include <iostream>
#include <stdlib.h>
#include <iostream>
#include <stdlib.h>
#include <unordered_map>

#include "verilated.h"
#include "Vverilator_tb.h"
#include "banked_memory.h"
#include "banked_memory.cpp"

// Function prototypes

int main(int argc, char** argv) {
  /* initialize random seed: */
  srand (time(NULL));

  // Construct a VerilatedContext to hold simulation time, etc.
  const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

  // Set debug level, 0 is off, 9 is highest presently used
  // May be overridden by commandArgs argument parsing
  contextp->debug(0);

  // Randomization reset policy
  // May be overridden by commandArgs argument parsing
  contextp->randReset(2);

  // Verilator must compute traced signals
  contextp->traceEverOn(true);

  // Pass arguments so Verilated code can see them, e.g. $value$plusargs
  // This needs to be called before you create any model
  contextp->commandArgs(argc, argv);

  // Construct the Verilated model,
  Vverilator_tb* top = new Vverilator_tb(contextp.get(), "TOP");

  // Initialize input signals
  top->clk         = 0;
  top->rst         = 0;
  top->bmem_ready  = 0;
  top->bmem_raddr  = 0;
  top->bmem_rdata  = 0;
  top->bmem_rvalid = 0;

  // Generate random reset interval
  int end = (rand() % 10) + 2; // Random between 1 and 10

  // Create memory model
  BankedMemory bmem(std::stoi(argv[1]), argv[2], top);

  // Simulate until $finish
  while (!contextp->gotFinish()) {
    // Trigger reset
    if (contextp->time() > 0 && contextp->time() <= end) {
      top->rst = 1;  // Assert reset
    } else {
      top->rst = 0;  // Deassert reset
    }

    // Check violations
    if (top->bmem_read && top->bmem_write) {
      std::cerr << "ERROR: Simultaneous R/W\n" << std::endl;
      break;
    }

    // 1 timeprecision period passes...
    contextp->timeInc(1);

    // Toggle clock
    top->clk = !top->clk;

    // Drive signals on clock negedge
    if (!top->clk) {
      bmem.eval_mem();
    }

    // Evaluate model
    top->eval();
  }
  
  // Final model cleanup
  top->final();

  // Final simulation summary
  contextp->statsPrintSummary();

  return 0;
}