// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

package acc_dummy_insn_pkg;

  class dummy_insn_t;
    rand logic [31:0] instr_data;
    rand logic [31:0] instr_mask;
    rand logic [1:0] writeback;
    rand logic [2:0] use_rs;
    rand acc_pkg::op_sel_e op_a_mux;
    rand acc_pkg::op_sel_e op_b_mux;
    rand acc_pkg::op_sel_e op_c_mux;
    rand acc_pkg::imm_sel_e imm_a_mux;
    rand acc_pkg::imm_sel_e imm_b_mux;
    rand acc_pkg::imm_sel_e imm_c_mux;

    constraint instr_data_c {unique{instr_data & instr_mask};}
  endclass

  class dummy_insn_set_t #(
    parameter int NumInstr = 10
  );

   dummy_insn_t dummy_insn[NumInstr];

   function new;
     for (int i = 0; i<NumInstr; i++) begin
       dummy_insn[i].randomize();
     end
   endfunction

 endclass






endpackage
