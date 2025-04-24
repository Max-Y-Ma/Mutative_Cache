module arbiter
import cache_types::*;
#(
  parameter integer NUM_NODES = NUM_CACHE
) (
  input  logic                 clk,
  input  logic                 rst,

  output logic [NUM_NODES-1:0] gnt,
  input  logic [NUM_NODES-1:0] req,
  input  logic [NUM_NODES-1:0] busy
);

  // Arbiter Signals
  logic [NUM_NODES-1:0] priority_reg;
  logic [NUM_NODES-1:0] priority_next;
  logic                 grant_valid;
  int                   idx;

  // Utilize to stall the bus arbitration during transient states
  logic transient_stall;

  always_comb begin
    grant_valid = '0;
    priority_next = priority_reg;

    gnt = '0;
    transient_stall = |busy;

    for (int i = 0; i < NUM_NODES; i++) begin
      idx = (i + priority_reg) % NUM_NODES;
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
  property p_bus_busy_no_grant;
    @(posedge clk) disable iff (rst)
    busy |-> (gnt == 0);
  endproperty

  assert property (p_bus_busy_no_grant) else
  $error("ERROR: Request granted on cache busy!");

endmodule
