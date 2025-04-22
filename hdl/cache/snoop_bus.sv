module snoop_bus
import cache_types::*;
#(
  parameter integer NUM_NODES = NUM_CACHE,
  parameter type    DTYPE     = logic[XLEN-1:0]
) (
  input logic clk,

  // Arbiter Grant
  input logic [NUM_NODES-1:0] gnt,

  // Incoming Messages
  input DTYPE bus_tx [NUM_NODES],

  // Output Bus Wire
  output DTYPE bus_msg
);

  localparam integer IDX = $clog2(NUM_NODES);

  logic [IDX-1:0] gnt_idx;
  logic           grant_valid;

  // Onehot to Binary
  always_comb begin
    gnt_idx = '0;
    grant_valid = '0;
    for (int i = 0; i < NUM_NODES; i++) begin
      if (gnt[i]) begin
        gnt_idx = (IDX)'(i);
        grant_valid = '1;
      end
    end
  end

  // Snoop Bus Output
  always_ff @(posedge clk) begin
    bus_msg <= bus_tx[gnt_idx];
  end

  property p_gnt_one_hot;
    @(posedge clk)
    $onehot0(gnt);
  endproperty
  assert_p_gnt_one_hot: assert property (p_gnt_one_hot) else $error("gnt is not one-hot");

endmodule
