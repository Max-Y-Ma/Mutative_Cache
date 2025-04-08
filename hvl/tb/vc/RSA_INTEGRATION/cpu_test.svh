// Random Instruction Test w/o Hazards
class cpu_test_no_hazards extends uvm_test;
  `uvm_component_utils(cpu_test_no_hazards)

  // Environment, Sequence
  cpu_env env;
  cpu_nop_sequence seq;

  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Build Components and Setup Config Database
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = cpu_env::type_id::create("env", this);
    seq = cpu_nop_sequence::type_id::create("seq", this);
  endfunction : build_phase

  // Start Sequence
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("CPU_TEST_NO_HAZARDS", "Running CPU_TEST_NO_HAZARDS!", UVM_MEDIUM)
    seq.start(env.agent.sequencer);
    phase.drop_objection(this);
  endtask : run_phase

endclass : cpu_test_no_hazards

// Random Instruction Test w/ Hazards
class cpu_test_with_hazards extends uvm_test;
  `uvm_component_utils(cpu_test_with_hazards)

  // Environment, Sequence
  cpu_env env;
  cpu_sequence seq;

  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Build Components and Setup Config Database
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = cpu_env::type_id::create("env", this);
    seq = cpu_sequence::type_id::create("seq", this);
  endfunction : build_phase

  // Start Sequence
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("CPU_TEST_WITH_HAZARDS", "Running CPU_TEST_WITH_HAZARDS!", UVM_MEDIUM)
    seq.start(env.agent.sequencer);
    phase.drop_objection(this);
  endtask : run_phase

endclass : cpu_test_with_hazards

// Random Instructions Test w/ Hazards and Cache Memory Module
class cpu_test extends uvm_test;
  `uvm_component_utils(cpu_test)

  // Environment, Sequence
  cpu_env env;
  cpu_sequence seq;

  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Build Components, Adjust Monitor, and Setup Config Database
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = cpu_env::type_id::create("env", this);
    seq = cpu_sequence::type_id::create("seq", this);
    // Override Agent Monitor and Driver
    cpu_monitor::type_id::set_type_override(cpu_monitor_cached::get_type());
    cpu_driver::type_id::set_type_override(cpu_driver_cached::get_type());
  endfunction : build_phase

  // Start Sequence
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("CPU_TEST", "Running CPU_TEST!", UVM_MEDIUM)
    seq.start(env.agent.sequencer);
    phase.drop_objection(this);
  endtask : run_phase
endclass : cpu_test