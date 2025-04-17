module memory
import types::*;
(
  input   logic           clk,
  input   logic           rst,

  input   xbar_msg_t      xbar_in [NUM_CACHE],
  output  xbar_msg_t      xbar_out,
  input   bus_msg_t       bus_msg,
  output  logic           arbiter_busy
);

  logic [2**XLEN-1:0][CACHELINE_SIZE-1:0] mem;
  logic [2**XLEN-1:0][COHERENCE_BITS-1:0] state;
  logic [2**XLEN-1:0][COHERENCE_BITS-1:0] next_state;

  logic arbiter_busy_next;
  logic arbiter_busy_reg;

  // Coherence Bit Update Logic
  always_comb begin
    next_state = state;
    arbiter_busy_next = arbiter_busy_reg;

    if (bus_msg.valid) begin
      unique case (state[bus_msg.addr])
        MI : begin
          unique case (bus_msg.bus_tx)
            GETS, GETM: begin
              // Goto EORM
              next_state[bus_msg.addr] = MEORM;
            end
            PUTM: begin
              // Goto ID, arbiter_busy_next = '1
              next_state[bus_msg.addr] = MID;
              arbiter_busy_next = '1;
            end
            default: begin
            end
          endcase
        end
        MS : begin
          unique case (bus_msg.bus_tx)
            GETS: begin
              // Goto S
              next_state[bus_msg.addr] = MS;
            end
            GETM: begin
              // Goto EORM
              next_state[bus_msg.addr] = MEORM;
            end
            PUTM: begin
              // Goto SD, arbiter_busy_next = '1
              next_state[bus_msg.addr] = MSD;
              arbiter_busy_next = '1;
            end
            default: begin
            end
          endcase
        end
        MEORM : begin
          unique case (bus_msg.bus_tx)
            GETS: begin
              // Goto SD, arbiter_busy_next = '1
              next_state[bus_msg.addr] = MSD;
              arbiter_busy_next = '1;
            end
            GETM: begin
              // Goto EORM
              next_state[bus_msg.addr] = MEORM;
            end
            PUTM: begin
              // Goto EORMD, arbiter_busy_next = '1
              next_state[bus_msg.addr] = MEORMD;
              arbiter_busy_next = '1;
            end
            default: begin
            end
          endcase
        end
        // Atomic Transactions -> ID, SD, EORMD
        default: begin
        end
      endcase
    end
    else begin
      for (int i = 0; i < NUM_CACHE; i++) begin
        if (xbar_in[i].memory_flag) begin
          unique case (state[xbar_in[i].addr])
            MID : begin
              unique case (xbar_in[i].mmsg)
                DATA, NODATA, NODATAE: begin
                  // Goto I, arbiter_busy_next = '0
                  next_state[xbar_in[i].addr] = MI;
                  arbiter_busy_next = '0;
                end
                default: begin
                end
              endcase
            end
            MSD : begin
              unique case (xbar_in[i].mmsg)
                DATA, NODATA, NODATAE: begin
                  // Goto S, arbiter_busy_next = '0
                  next_state[xbar_in[i].addr] = MS;
                  arbiter_busy_next = '0;
                end
                default: begin
                end
              endcase
            end
            MEORMD : begin
              unique case (xbar_in[i].mmsg)
                DATA, NODATAE: begin
                  // Goto I, arbiter_busy_next = '0
                  next_state[xbar_in[i].addr] = MI;
                  arbiter_busy_next = '0;
                end
                NODATA: begin
                  // Goto EORM, arbiter_busy_next = '0
                  next_state[xbar_in[i].addr] = MEORM;
                  arbiter_busy_next = '0;
                end
                default: begin
                end
              endcase
            end
            // Ignore Transactions -> I, S, EORM
            default: begin
            end
          endcase
        end
      end
    end
  end

  assign arbiter_busy = arbiter_busy_next | arbiter_busy_reg;

  // Bus Request Update Logic
  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 0; i < 2**XLEN; i++) begin
        mem[i] <= CACHELINE_SIZE'(i);
        state[i] <= MI;
      end
      arbiter_busy_reg <= '0;
    end else begin
      xbar_out <= '0;

      if (bus_msg.valid) begin
        unique case (state[bus_msg.addr])
          MI : begin
            unique case (bus_msg.bus_tx)
              GETS: begin
                // Send Data to Requestor (Exclusive)
                xbar_out.valid       <= '1;
                xbar_out.destination <= bus_msg.source;
                xbar_out.memory_flag <= '0;
                xbar_out.addr        <= bus_msg.addr;
                xbar_out.data        <= mem[bus_msg.addr];
                xbar_out.mmsg        <= EXCLUSIVE;
              end
              GETM: begin
                // Send Data to Requestor
                xbar_out.valid       <= '1;
                xbar_out.destination <= bus_msg.source;
                xbar_out.memory_flag <= '0;
                xbar_out.addr        <= bus_msg.addr;
                xbar_out.data        <= mem[bus_msg.addr];
                xbar_out.mmsg        <= DATA;
              end
              default: begin
              end
            endcase
          end
          MS : begin
            unique case (bus_msg.bus_tx)
              GETS: begin
                // Send Data to Requestor (Exclusive)
                xbar_out.valid       <= '1;
                xbar_out.destination <= bus_msg.source;
                xbar_out.memory_flag <= '0;
                xbar_out.addr        <= bus_msg.addr;
                xbar_out.data        <= mem[bus_msg.addr];
                xbar_out.mmsg        <= DATA;
              end
              GETM: begin
                // Send Data to Requestor
                xbar_out.valid       <= '1;
                xbar_out.destination <= bus_msg.source;
                xbar_out.memory_flag <= '0;
                xbar_out.addr        <= bus_msg.addr;
                xbar_out.data        <= mem[bus_msg.addr];
                xbar_out.mmsg        <= DATA;
              end
              default: begin
              end
            endcase
          end
          // Ignore Transactions -> EORM, ID, SD, EORMD
          default: begin
          end
        endcase
      end else begin
        for (int i = 0; i < NUM_CACHE; i++) begin
          if (xbar_in[i].memory_flag) begin
            unique case (state[bus_msg.addr])
              MID : begin
                unique case (xbar_in[i].mmsg)
                  DATA: begin
                    // Write Data to Memory
                    mem[xbar_in[i].addr] <= xbar_in[i].data;
                  end
                  default: begin
                  end
                endcase
              end
              MSD : begin
                unique case (xbar_in[i].mmsg)
                  DATA: begin
                    // Write Data to Memory
                    mem[xbar_in[i].addr] <= xbar_in[i].data;
                  end
                  default: begin
                  end
                endcase
              end
              MEORMD : begin
                unique case (xbar_in[i].mmsg)
                  DATA: begin
                    // Write Data to Memory
                    mem[xbar_in[i].addr] <= xbar_in[i].data;
                  end
                  default: begin
                  end
                endcase
              end
              // Ignore Transactions -> I, S, EORM
              default: begin
              end
            endcase
          end
        end
      end

      // Update Coherence State Logic
      for (int i = 0; i < 2**XLEN; i++) begin
        state[i] <= next_state[i];
      end

      arbiter_busy_reg <= arbiter_busy_next;
    end
  end

  // Check that bus and xbar are not both valid
  logic xbar_valid;
  always_comb begin
    xbar_valid = '0;
    for (int i = 0; i < NUM_CACHE; i++) begin
      xbar_valid |= xbar_in[i].valid;
    end
  end

  property p_bus_xbar_onehot0;
    @(posedge clk) disable iff (rst)
    $onehot0({bus_msg.valid, xbar_valid});
  endproperty

  assert property (p_bus_xbar_onehot0) else
  $error("ERROR: bus_msg.valid and xbar_valid both high!");

  // Check that all memory addresses have been accessed
  for (genvar i = 0; i < 2**XLEN; i++) begin : gen_bus_msg_addr_accesssed
    cover_bus_msg_addr_accessed: cover property (@(posedge clk) bus_msg.addr == i);
  end

  // Check that all coherence states have been reached for each memory address
  for (genvar i = 0; i < 2**XLEN; i++) begin : gen_memory_coherence_states
    cover_memory_coherence_states_MI: cover property (@(posedge clk) state[i] == MI);
    cover_memory_coherence_states_MS: cover property (@(posedge clk) state[i] == MS);
    cover_memory_coherence_states_MEORM: cover property (@(posedge clk) state[i] == MEORM);
    cover_memory_coherence_states_MSD: cover property (@(posedge clk) state[i] == MSD);
    cover_memory_coherence_states_MEORMD: cover property (@(posedge clk) state[i] == MEORMD);
  end

endmodule
