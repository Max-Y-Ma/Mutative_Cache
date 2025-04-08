module detection_unit
import rv32imc_types::*;
(
  input  logic       ex_mem_read,
  input  logic [4:0] ex_rd_addr,
  input  logic [4:0] rs1_addr,
  input  logic [4:0] rs2_addr,
  output logic       load_hazard
);

// Hazard Detection Logic
always_comb begin
  // Default Signals
  load_hazard = 1'b0;

  // If the instruction in execute stage is load:
  // Stall 1 cycle, then execute stage will handle forwarding
  if (ex_mem_read && ((rs1_addr == ex_rd_addr) || (rs2_addr == ex_rd_addr))) begin
    load_hazard = 1'b1;
  end
end

endmodule : detection_unit
