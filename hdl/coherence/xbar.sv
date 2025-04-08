module xbar
import types::*;
(
  input   logic      clk,
  input   logic      rst,
  input   xbar_msg_t xbar_in  [NUM_CPUS+1],
  output  xbar_msg_t xbar_out [NUM_CPUS+1][NUM_CPUS]
);

  /*
  Assuming NUM_CPUS = 4
  O[0][0] = I[1]
  O[0][1] = I[2]
  O[0][2] = I[3]
  O[0][3] = I[4]

  O[1][0] = I[0]
  O[1][1] = I[2]
  O[1][2] = I[3]
  O[1][3] = I[4]

  ...

  This goes to memory controller
  O[4][0] = I[0]
  O[4][1] = I[1]
  O[4][2] = I[2]
  O[4][3] = I[3]
  */

  for (genvar i = 0; i < NUM_CPUS + 1; i++) begin : gen_xbar_out_gen
    for (genvar j = 0; j < NUM_CPUS; j++) begin : gen_xbar_in_gen
      always_comb begin
        if (j >= i) begin
          xbar_out[i][j] = xbar_in[j + 1];
        end else begin
          xbar_out[i][j] = xbar_in[j];
        end
      end
    end
  end

  // Only one signal is valid in xbar_in at a time
  logic [NUM_CPUS:0] xbar_valid;
  always_comb begin
    for (int i = 0; i < NUM_CPUS + 1; i++) begin
      xbar_valid[i] = xbar_in[i].valid;
    end
  end

  property p_xbar_valid_onehot;
    @(posedge clk) disable iff (rst)
    $onehot0(xbar_valid) || (xbar_valid == 0);
  endproperty

  assert property (p_xbar_valid_onehot) else
  $error("ERROR: xbar_valid is not onehot!");

  // All valid signals in xbar_in have been high
  for (genvar i = 0; i < NUM_CPUS + 1; i++) begin : gen_xbar_cover_valid
    cover_xbar_valid: cover property (@(posedge clk) xbar_in[i].valid == 1);
  end

  // All destination locations are covered
  for (genvar i = 0; i < NUM_CPUS + 1; i++) begin : gen_xbar_destination_out
    for (genvar j = 0; j < NUM_CPUS; j++) begin : gen_xbar_destination_in
      if (j >= i) begin : gen_xbar_destination_skip
        cover_xbar_destination: cover property (@(posedge clk) xbar_in[i].destination == j + 1);
      end else begin : gen_xbar_destination
        cover_xbar_destination: cover property (@(posedge clk) xbar_in[i].destination == j);
      end
    end
  end

  // Memory flag was set
  for (genvar i = 0; i < NUM_CPUS; i++) begin : gen_xbar_memory_flag
    cover_xbar_memory_flag: cover property (@(posedge clk) xbar_in[i].memory_flag == 1);
  end

  // All xbar message types were hit for every xbar_in
  for (genvar i = 0; i < NUM_CPUS; i++) begin : gen_xbar_memory_type
    cover_xbar_memory_type_DATA: cover property (@(posedge clk) xbar_in[i].mmsg == DATA);
    cover_xbar_memory_type_NODATA: cover property (@(posedge clk) xbar_in[i].mmsg == NODATA);
    cover_xbar_memory_type_NODATAE: cover property (@(posedge clk) xbar_in[i].mmsg == NODATAE);
  end

  cover_xbar_memory_type_memory_controller_DATA:
  cover property (@(posedge clk) xbar_in[NUM_CPUS].mmsg == DATA);

  cover_xbar_memory_type_memory_controller_EXCLUSIVE:
  cover property (@(posedge clk) xbar_in[NUM_CPUS].mmsg == EXCLUSIVE);

endmodule
