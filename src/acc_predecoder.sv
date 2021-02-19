// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

module acc_predecoder #(
  parameter int     NumInstr             = -1,
  parameter acc_pkg::offl_instr_t OfflInstr[NumInstr] = {-1}
) (

  input acc_pkg::prd_req_t prd_req_i,
  output acc_pkg::prd_rsp_t prd_rsp_o
);

  import acc_pkg::*;

  imm_sel_e imm_a_mux;
  imm_sel_e imm_b_mux;
  imm_sel_e imm_c_mux;

  always_comb begin
    prd_rsp_o.p_accept     = 1'b0;
    prd_rsp_o.p_writeback = '0;
    prd_rsp_o.p_use_rs    = '0;
    prd_rsp_o.p_op_a_mux  = OP_RS;
    prd_rsp_o.p_op_b_mux  = OP_RS;
    prd_rsp_o.p_op_c_mux  = OP_RS;
    prd_rsp_o.p_imm_a_mux = IMM_I;
    prd_rsp_o.p_imm_b_mux = IMM_I;
    prd_rsp_o.p_imm_c_mux = IMM_I;
    for (int unsigned i = 0; i<NumInstr; i++) begin
      if ((OfflInstr[i].instr_mask & prd_req_i.q_instr_data) == OfflInstr[i].instr_data) begin
        prd_rsp_o.p_accept    = 1'b1;
        prd_rsp_o.p_writeback = OfflInstr[i].prd_rsp.p_writeback;
        prd_rsp_o.p_use_rs    = OfflInstr[i].prd_rsp.p_use_rs;
        prd_rsp_o.p_op_a_mux  = OfflInstr[i].prd_rsp.p_op_a_mux;
        prd_rsp_o.p_op_b_mux  = OfflInstr[i].prd_rsp.p_op_b_mux;
        prd_rsp_o.p_op_c_mux  = OfflInstr[i].prd_rsp.p_op_c_mux;
        prd_rsp_o.p_imm_a_mux = OfflInstr[i].prd_rsp.p_imm_a_mux;
        prd_rsp_o.p_imm_b_mux = OfflInstr[i].prd_rsp.p_imm_b_mux;
        prd_rsp_o.p_imm_c_mux = OfflInstr[i].prd_rsp.p_imm_c_mux;
        break;
      end
    end
  end

endmodule


`include "acc_interface/assign.svh"

module acc_predecoder_intf #(
  parameter int NumInstr = -1,
  parameter acc_pkg::offl_instr_t OfflInstr[NumInstr] = {-1}
) (
  ACC_PREDECODER_BUS prd
);

  acc_pkg::prd_req_t prd_req;
  acc_pkg::prd_rsp_t prd_rsp;

  `ACC_PREDECODER_ASSIGN_TO_RESP(prd_rsp, prd)
  `ACC_PREDECODER_ASSIGN_FROM_REQ(prd, prd_req)


  acc_predecoder #(
    .NumInstr  ( NumInstr  ),
    .OfflInstr ( OfflInstr )
  ) acc_predecoder_i (
    .prd_req_i(prd_req),
    .prd_rsp_o(prd_rsp)
  );

endmodule

