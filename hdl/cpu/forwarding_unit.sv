module forwarding_unit 
import rv32imc_types::*;
(
  input  logic [4:0]   rs1_addr,
  input  logic [4:0]   rs2_addr,
  input  logic [4:0]   ex_rd_addr,
  input  logic [4:0]   mem_rd_addr,
  input  logic         ex_regf_we,
  input  logic         mem_regf_we,
  output forward_mux_t fwd_src_a,
  output forward_mux_t fwd_src_b
);

// Execution and Data Memory Stage Hazard
always_comb begin
  // Default Signals
  fwd_src_a = id_source;
  fwd_src_b = id_source;

  // Execution Conditions
  if (ex_regf_we && (ex_rd_addr != 0) && (ex_rd_addr == rs1_addr)) begin
    fwd_src_a = ex_source;
  end else if (mem_regf_we && (mem_rd_addr != 0) && (mem_rd_addr == rs1_addr)) begin
    fwd_src_a = mem_source;
  end

  // Data Memory Conditions
  if (ex_regf_we && (ex_rd_addr != 0) && (ex_rd_addr == rs2_addr)) begin
    fwd_src_b = ex_source;
  end else if (mem_regf_we && (mem_rd_addr != 0) && (mem_rd_addr == rs2_addr)) begin
    fwd_src_b = mem_source;
  end
end

endmodule : forwarding_unit
