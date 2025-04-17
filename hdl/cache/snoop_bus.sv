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

  logic [$clog2(NUM_NODES)-1:0] gnt_idx;
  logic grant_valid;

  always_comb begin
    gnt_idx = '0;
    grant_valid = '0;
    for (int i = 0; i < NUM_NODES; i++) begin
      if (gnt[i]) begin
        gnt_idx = ($clog2(NUM_NODES))'(i);
        grant_valid = '1;
      end
    end
  end

  always_ff @(posedge clk) begin
    bus_msg <= '{
      valid: grant_valid,
      source: gnt_idx,
      addr: bus_addr[gnt_idx],
      bus_tx: bus_tx[gnt_idx]
    };
  end

  property p_gnt_one_hot;
    @(posedge clk)
    $onehot0(gnt) || (gnt == 0);
  endproperty
  assert_p_gnt_one_hot: assert property (p_gnt_one_hot) else $error("gnt is not one-hot");

  // All bus sources have been able to send a request
  for (genvar i = 0; i < NUM_NODES; i++) begin : gen_snoop_gnt
    cover_snoop_gnt: cover property (@(posedge clk) gnt[i] == 1);
  end

  // All bus message types have been sent
  for (genvar i = 0; i < NUM_NODES; i++) begin : gen_snoop_message_types
    cover_snoop_message_types_GETS: cover property (@(posedge clk) bus_tx[i] == GETS);
    cover_snoop_message_types_GETM: cover property (@(posedge clk) bus_tx[i] == GETM);
    cover_snoop_message_types_PUTM: cover property (@(posedge clk) bus_tx[i] == PUTM);
  end

endmodule
