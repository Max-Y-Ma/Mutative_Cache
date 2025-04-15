// Top UVM Test Package for RISV Pipeline CPU
`include "cpu_config.svh"

package cpu_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import rv32imc_types::*;

  `include "cpu_sequence.svh"
  `include "cpu_agent.svh"
  `include "cpu_env.svh"
  `include "cpu_test.svh"
endpackage