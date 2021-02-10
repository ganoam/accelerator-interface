// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

module acc_predecoder #(
  parameter type    instr_t              = acc_pkg::offl_instr_t,
  parameter int     NumInstr             = -1,
  parameter instr_t offl_instr[NumInstr] = {-1}
) (
  input  logic [31:0]       instr_rdata_i,
  output logic              offl_accept_o,
  output logic [1:0]        offl_writeback_o,
  output logic [2:0]        offl_use_rs_o,
  output acc_pkg::op_sel_e  offl_op_a_mux_o,
  output acc_pkg::op_sel_e  offl_op_b_mux_o,
  output acc_pkg::op_sel_e  offl_op_c_mux_o,
  output acc_pkg::imm_sel_e offl_imm_a_mux_o,
  output acc_pkg::imm_sel_e offl_imm_b_mux_o,
  output acc_pkg::imm_sel_e offl_imm_c_mux_o
);

  import acc_pkg::*;

  imm_sel_e imm_a_mux;
  imm_sel_e imm_b_mux;
  imm_sel_e imm_c_mux;


  always_comb begin
    offl_accept_o    = 1'b0;
    offl_writeback_o = '0;
    offl_use_rs_o    = '0;
    offl_op_a_mux_o  = OP_RS;
    offl_op_b_mux_o  = OP_RS;
    offl_op_c_mux_o  = OP_RS;
    offl_imm_a_mux_o   = IMM_I;
    offl_imm_b_mux_o   = IMM_I;
    offl_imm_c_mux_o   = IMM_I;
    for (int unsigned i=0; i<NumInstr; i++) begin
      if (offl_instr[i].instr_mask & instr_rdata_i == offl_instr[i].instr_data) begin
        offl_accept_o    = 1'b1;
        offl_writeback_o = offl_instr[i].writeback;
        offl_use_rs_o    = offl_instr[i].use_rs;
        offl_op_a_mux_o  = offl_instr[i].op_a_mux;
        offl_op_b_mux_o  = offl_instr[i].op_b_mux;
        offl_op_c_mux_o  = offl_instr[i].op_c_mux;
        offl_imm_a_mux_o   = offl_instr[i].imm_a_mux;
        offl_imm_b_mux_o   = offl_instr[i].imm_b_mux;
        offl_imm_c_mux_o   = offl_instr[i].imm_c_mux;
        break;
      end
    end
  end

endmodule

