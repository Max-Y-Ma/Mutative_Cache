module arbiter
import types::*;
(
  input logic clk,
  input logic rst,

  input  logic [NUM_CPUS-1:0] req,
  output logic [NUM_CPUS-1:0] gnt,

  input logic [NUM_CPUS:0]    busy
);

  logic [NUM_CPUS-1:0] priority_reg;
  logic [NUM_CPUS-1:0] priority_next;
  logic grant_valid;
  int idx;
  logic transient_stall; // Utilized to stall the bus arbitration during transient states

  always_comb begin
    grant_valid = '0;
    priority_next = priority_reg;

    gnt = '0;
    transient_stall = |busy;

    for (int i = 0; i < NUM_CPUS; i++) begin
      idx = (i + priority_reg) % NUM_CPUS;
      if (!grant_valid && req[idx] && !transient_stall) begin
        gnt[idx] = '1;
        grant_valid = '1;
        priority_next = idx + 1; // Update priority to next CPU
      end
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      priority_reg <= '0;
    end else begin
      priority_reg <= priority_next;
    end
  end

  // No bus grants are given when a core is busy
  property p_bus_busy;
    @(posedge clk) disable iff (rst)
    |busy |-> (|gnt == 0);
  endproperty

  assert property (p_bus_busy) else
  $error("ERROR: Request granted on cache busy!");

endmodule
