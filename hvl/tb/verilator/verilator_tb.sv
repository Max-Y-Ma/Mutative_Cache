module verilator_tb 
(
  input logic         clk,
  input logic         rst,

  output logic [31:0] bmem_addr,
  output logic        bmem_read,
  output logic        bmem_write,
  output logic [63:0] bmem_wdata,
  input  logic        bmem_ready,

  input  logic [31:0] bmem_raddr,
  input  logic [63:0] bmem_rdata,
  input  logic        bmem_rvalid,

  output logic        halt,
  output logic        error
);

// Monitor Interface
verilator_mon_itf mon_itf(.*);    
verilator_monitor monitor(.itf(mon_itf));

// DUT Instantiation
core dut(
  .clk            (clk),
  .rst            (rst),

  .bmem_addr      (bmem_addr),
  .bmem_read      (bmem_read),
  .bmem_write     (bmem_write),
  .bmem_wdata     (bmem_wdata),
  .bmem_ready     (bmem_ready),

  .bmem_raddr     (bmem_raddr),
  .bmem_rdata     (bmem_rdata),
  .bmem_rvalid    (bmem_rvalid)
);

// Monitor Interface DUT Wiring
`include "../../chip/tb/vc/core/rvfi_reference.svh"

assign error = mon_itf.error;
assign halt = mon_itf.halt;

longint lcom;
longint cycles;
longint total_cycles;

// Cycle Progress Logging
int fd;
initial fd = $fopen("./progress.ansi", "w");
final $fclose(fd);

always_ff @ (posedge clk) begin
  if (rst) begin
    cycles = '0;
    total_cycles = '0;
  end
  else begin
    cycles++;
    total_cycles++;

    if (mon_itf.order % 1000 == 0 && mon_itf.order != lcom && mon_itf.valid) begin
      $fwrite(fd, "COMMIT %8d -- CYCLES: %8d -- IPC 1000: %f -- CUM IPC: %f\n", mon_itf.order,
              total_cycles, real'(1000)/cycles, real'(mon_itf.order)/total_cycles);
      cycles = '0;
      lcom = mon_itf.order;
    end
  end  
end

// Print some stuff as an example
initial begin
  $dumpfile("waveform.vcd");
  $dumpvars();
end

// End Condition
int timeout_cycles = 100000000;
always @(posedge clk) begin
  if (mon_itf.halt) begin
    $finish;
  end
  if (timeout_cycles == 0) begin
    $display("");
    $display("==================");
    $display("Testbench Timeout!");
    $display("==================");
    $display("");
    $finish;
  end
  if (mon_itf.error != 0) begin
    $display("");
    $display("================");
    $display("Testbench Error!");
    $display("================");
    $display("");
    $finish;
  end
  timeout_cycles <= timeout_cycles - 1;
end

endmodule : verilator_tb
