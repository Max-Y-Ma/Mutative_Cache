// Agent, Sequencer, Driver, Monitor Classes for Test Environment of RISCV Pipeline CPU
typedef uvm_sequencer #(cpu_rand_instr) cpu_sequencer;

// Random Instruction Test w/o Hazards
class cpu_nop_sequence extends uvm_sequence #(cpu_rand_instr);
  `uvm_object_utils(cpu_nop_sequence)

  // Constructor
  function new(string name = "");
    super.new(name);
  endfunction : new

  // Sequence Body
  task body;
    // Transaction Handle
    cpu_rand_instr blueprint, txn;
    blueprint = new();

    repeat(`NUM_TEST) begin
      // Send randomized instruction to sequencer
      txn = blueprint;
      blueprint.instr.randomize();
      start_item(txn);
      finish_item(txn);

      // Follow with 5 nops to avoid hazards
      repeat(5) begin
        txn = blueprint;
        blueprint.instr.instr.word = `NOP_INSTR;
        start_item(txn);
        finish_item(txn);
      end
    end
  endtask : body

endclass : cpu_nop_sequence

// Random Instructions Test w/ Hazards
class cpu_sequence extends uvm_sequence #(cpu_rand_instr);
  `uvm_object_utils(cpu_sequence)

  // Constructor
  function new(string name = "");
    super.new(name);
  endfunction : new

  // Sequence Body
  task body;
    // Transaction Handle
    cpu_rand_instr blueprint, txn;
    blueprint = new();

    repeat(`NUM_TEST) begin
      // Send randomized instruction to sequencer
      txn = blueprint;
      blueprint.instr.randomize();
      start_item(txn);
      finish_item(txn);
    end
  endtask : body

endclass : cpu_sequence

// RISCV Pipeline CPU Driver: Drive Instructions as DUT Stimulus
class cpu_driver extends uvm_driver #(cpu_rand_instr);
  `uvm_component_utils(cpu_driver)

  // DUT Instruction Interface
  virtual mem_itf mif;

  // Analysis Port
  uvm_analysis_port #(cpu_rand_instr) aport;

  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Grab Instruction Memory Interface
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Create Analysis Port
    aport = new("aport", this);
    `uvm_info("CPU_DRIVER", "Created CPU_DRIVER!", UVM_MEDIUM)
    // Configuration Database
    if (!uvm_config_db #(virtual mem_itf)::get(this, "", "mem_itf_i", mif)) begin
      `uvm_fatal("CPU_DRIVER", "DUT Interface not defined! Simulation aborted!");
    end
  endfunction : build_phase

  // Drive DUT Signals and Sample Coverage
  task run_phase(uvm_phase phase);
    cpu_rand_instr txn;

    forever begin
      // Get Instruction Transaction
      seq_item_port.get_next_item(txn);

      // Send to Coverage
      aport.write(txn);
      
      // Drive Signals
      while(1) begin
        @(posedge mif.clk) begin
          if (mif.rst) begin
            mif.rdata <= 'x;
            mif.resp <= 1'b0;
          end else if (|mif.rmask) begin
            for (int i = 0; i < 4; i++) begin
              if (mif.rmask[i]) begin
                mif.rdata[i*8+:8] <= txn.instr.instr.word[i*8+:8];
              end else begin
                mif.rdata[i*8+:8] <= 'x;
              end
            end
            mif.resp <= 1'b1;

            // Finish Driving Signals
            seq_item_port.item_done();
            break;
          end else begin
            mif.rdata <= 'x;
            mif.resp <= 1'b0;
          end
        end
      end
    end
  endtask : run_phase 

endclass : cpu_driver

// RISCV Pipeline CPU Driver: Drive Cached Instructions as DUT Stimulus 
class cpu_driver_cached extends cpu_driver;
  `uvm_component_utils(cpu_driver_cached)

  // DUT Instruction Interface
  virtual mem_itf mif;

  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Grab Instruction Memory Interface
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Create Analysis Port
    `uvm_info("CPU_DRIVER_CACHED", "Created CPU_DRIVER_CACHED!", UVM_MEDIUM)
    // Configuration Database
    if (!uvm_config_db #(virtual mem_itf)::get(this, "", "mem_itf_i", mif)) begin
      `uvm_fatal("CPU_DRIVER_CACHED", "DUT Interface not defined! Simulation aborted!");
    end
  endfunction : build_phase

  // Drive DUT Signals and Sample Coverage
  task run_phase(uvm_phase phase);
    cpu_rand_instr txn;

    logic [31:0] internal_memory_array [logic [31:2]];
    logic [31:0] i_cached_addr;
    logic [3:0]  i_cached_rmask;
    logic [31:0] tag_i [logic [2:0]];
    int          i_delay;

    forever begin
      // Get Instruction Transaction
      seq_item_port.get_next_item(txn);

      // Send to Coverage
      aport.write(txn);
      
      // Drive Signals
      while(1) begin
        @(posedge mif.clk) begin
          i_cached_addr = mif.addr;
          i_cached_rmask = mif.rmask;
          if (mif.rst) begin
            mif.rdata <= 'x;
            mif.resp <= 1'b0;
          end else if (|i_cached_rmask) begin
            if (tag_i[i_cached_addr[4:2]] != i_cached_addr) begin
              mif.resp <= 1'b0;
              std::randomize(i_delay) with {
                i_delay dist {
                  [5:7] := 80,
                  [8:15] := 20
                };
              };
              repeat (i_delay) @(posedge mif.clk);
              tag_i[i_cached_addr[4:2]] = i_cached_addr;
            end
            for (int i = 0; i < 4; i++) begin
              if (i_cached_rmask[i]) begin
                mif.rdata[i*8+:8] <= txn.instr.instr.word[i*8+:8];
              end else begin
                mif.rdata[i*8+:8] <= 'x;
              end
            end
            mif.resp <= 1'b1;

            // Finish Driving Signals
            seq_item_port.item_done();
            break;
          end else begin
            mif.rdata <= 'x;
            mif.resp <= 1'b0;
          end
        end
      end
    end
  endtask : run_phase 

endclass : cpu_driver_cached

// RISCV Pipeline CPU Monitor: Response to DUT Data Memory Signals
class cpu_monitor extends uvm_monitor;
  `uvm_component_utils(cpu_monitor)

  // DUT Data Memory Interface
  virtual mem_itf mif;

  bit [31:0] internal_memory_array [logic [31:2]];

  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Grab Data Memory Interface
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("CPU_MONITOR", "Created CPU_MONITOR!", UVM_MEDIUM)
    // Configuration Database
    if (!uvm_config_db #(virtual mem_itf)::get(this, "", "mem_itf_d", mif)) begin
      `uvm_fatal("CPU_MONITOR", "DUT Interface not defined! Simulation aborted!");
    end
  endfunction : build_phase

  // Response to Data Memory Requests
  task run_phase(uvm_phase phase);
    forever begin
      // Response to Instruction Memory Transactions
      @(posedge mif.clk) begin
        if (mif.rst) begin
          mif.rdata <= 'x;
          mif.resp <= 1'b0;
        end else if (|mif.rmask) begin
          for (int i = 0; i < 4; i++) begin
            if (mif.rmask[i]) begin
              mif.rdata[i*8+:8] <= internal_memory_array[mif.addr[31:2]][i*8+:8];
            end else begin
              mif.rdata[i*8+:8] <= 'x;
            end
          end
          mif.resp <= 1'b1;
        end else if (|mif.wmask) begin
          for (int i = 0; i < 4; i++) begin
            if (mif.wmask[i]) begin
              internal_memory_array[mif.addr[31:2]][i*8+:8] = mif.wdata[i*8+:8];
            end
          end
          mif.resp <= 1'b1;
        end else begin
          mif.rdata <= 'x;
          mif.resp <= 1'b0;
        end
      end
    end
  endtask : run_phase

endclass : cpu_monitor

// RISCV Pipeline CPU Monitor: Response to DUT Cached Data Memory Signals
class cpu_monitor_cached extends cpu_monitor;
  `uvm_component_utils(cpu_monitor_cached)

  // DUT Data Memory Interface
  virtual mem_itf mif;

  bit [31:0] internal_memory_array [logic [31:2]];

  bit [31:0] tag_i [logic [2:0]];
  bit [31:0] tag_d [logic [2:0]];

  int i_delay;
  int d_delay;

  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Grab Data Memory Interface
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("CPU_MONITOR_CACHED", "Created CPU_MONITOR_CACHED!", UVM_MEDIUM)
    // Configuration Database
    if (!uvm_config_db #(virtual mem_itf)::get(this, "", "mem_itf_d", mif)) begin
      `uvm_fatal("CPU_MONITOR_CACHED", "DUT Interface not defined! Simulation aborted!");
    end
  endfunction : build_phase

  // Response to Data Memory Requests
  task run_phase(uvm_phase phase);
    // Response to Instruction Memory Transactions
    forever begin
      @(posedge mif.clk) begin
        logic [31:0] d_cached_addr;
        logic [3:0]  d_cached_rmask;
        logic [3:0]  d_cached_wmask;
        logic [31:0] d_cached_wdata;
        d_cached_addr  = mif.addr;
        d_cached_rmask = mif.rmask;
        d_cached_wmask = mif.wmask;
        d_cached_wdata = mif.wdata;
        if (mif.rst) begin
          mif.rdata <= 'x;
          mif.resp <= 1'b0;
        end else if (|d_cached_rmask) begin
          begin
            if (tag_d[d_cached_addr[4:2]] != d_cached_addr) begin
              mif.resp <= 1'b0;
              std::randomize(d_delay) with {
                d_delay dist {
                  [5:7] := 80,
                  [8:15] := 20
                };
              };
              repeat (d_delay) @(posedge mif.clk);
              tag_d[d_cached_addr[4:2]] = d_cached_addr;
            end
            for (int i = 0; i < 4; i++) begin
              if (d_cached_rmask[i]) begin
                mif.rdata[i*8+:8] <= internal_memory_array[d_cached_addr[31:2]][i*8+:8];
              end else begin
                mif.rdata[i*8+:8] <= 'x;
              end
            end
            mif.resp <= 1'b1;
          end
        end else if (|d_cached_wmask) begin
          begin
            if (tag_d[d_cached_addr[4:2]] != d_cached_addr) begin
              mif.resp <= 1'b0;
              std::randomize(d_delay) with {
                d_delay dist {
                  [5:7] := 80,
                  [8:15] := 20
                };
              };
              repeat (d_delay) @(posedge mif.clk);
              tag_d[d_cached_addr[4:2]] = d_cached_addr;
            end
            for (int i = 0; i < 4; i++) begin
              if (d_cached_wmask[i]) begin
                internal_memory_array[d_cached_addr[31:2]][i*8+:8] = d_cached_wdata[i*8+:8];
              end
            end
            mif.resp <= 1'b1;
          end
        end else begin
          mif.rdata <= 'x;
          mif.resp <= 1'b0;
        end
      end
    end
  endtask : run_phase

endclass : cpu_monitor_cached

class cpu_agent extends uvm_agent;
  `uvm_component_utils(cpu_agent)

  // Analysis Port
  uvm_analysis_port #(cpu_rand_instr) aport;

  // Driver, Monitor
  cpu_sequencer sequencer;
  cpu_driver driver;
  cpu_monitor monitor;

  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Create Ports and Components
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Create Analysis Port
    aport = new("aport", this);
    // Create Sequencer
    sequencer = cpu_sequencer::type_id::create("sequencer", this);
    // Create Driver
    driver = cpu_driver::type_id::create("driver", this);
    // Create Monitor
    monitor = cpu_monitor::type_id::create("monitor", this);
  endfunction : build_phase

  // Connect Ports 
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect Analysis Port w/ Driver
    driver.aport.connect(aport);
    // Connect Driver w/ Sequencer
    driver.seq_item_port.connect(sequencer.seq_item_export);
  endfunction : connect_phase

endclass : cpu_agent