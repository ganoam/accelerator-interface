// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

module acc_predecoder #(
  parameter int     NumInstr             = -1,
  parameter acc_pkg::offl_instr_t offl_instr[NumInstr] = {-1}
) (
  input  logic [31:0] instr_rdata_i,
  output logic        offl_accept_o,

  output acc_pkg::offl_instr_t offl_instr_o
);

  import acc_pkg::*;

  imm_sel_e imm_a_mux;
  imm_sel_e imm_b_mux;
  imm_sel_e imm_c_mux;

  always_comb begin
    offl_accept_o          = 1'b0;
    offl_instr_o.writeback = '0;
    offl_instr_o.use_rs    = '0;
    offl_instr_o.op_a_mux  = OP_RS;
    offl_instr_o.op_b_mux  = OP_RS;
    offl_instr_o.op_c_mux  = OP_RS;
    offl_instr_o.imm_a_mux = IMM_I;
    offl_instr_o.imm_b_mux = IMM_I;
    offl_instr_o.imm_c_mux = IMM_I;
    for (int unsigned i = 0; i<NumInstr; i++) begin
      if ((offl_instr[i].instr_mask & instr_rdata_i) == offl_instr[i].instr_data) begin
        offl_accept_o          = 1'b1;
        offl_instr_o.writeback = offl_instr[i].writeback;
        offl_instr_o.use_rs    = offl_instr[i].use_rs;
        offl_instr_o.op_a_mux  = offl_instr[i].op_a_mux;
        offl_instr_o.op_b_mux  = offl_instr[i].op_b_mux;
        offl_instr_o.op_c_mux  = offl_instr[i].op_c_mux;
        offl_instr_o.imm_a_mux = offl_instr[i].imm_a_mux;
        offl_instr_o.imm_b_mux = offl_instr[i].imm_b_mux;
        offl_instr_o.imm_c_mux = offl_instr[i].imm_c_mux;
        break;
      end
    end
  end

endmodule

