// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

package acc_pkg;
  // TODO: define common cluster parameters in package

  // Helper Functions for *constant* localparam definitions.
  // array functions (e.g.  'arr.sum()') return queue type which is not
  // considered constant for use as parameter.

  // TODO: put in cf_math_pkg or something?? Any better ideas?
  function automatic int max (input int a, b);
    return a>b ? a : b;
  endfunction

  function automatic int maxn (input int arr[], n);
    return n == 0 ? arr[0] : max(arr[n-1], maxn(arr, n-1));
  endfunction

  function automatic int sum (input int a, b);
    return a+b;
  endfunction

  function automatic int sumn (input int arr[], n);
    return n==0 ? arr[0] : sum(arr[n-1], sumn(arr, n-1));
  endfunction

  typedef enum logic[1:0] {
    OP_RS,
    OP_IMM
  } op_sel_e;

  // Immediate b selection
  typedef enum logic [2:0] {
    IMM_I,
    IMM_S,
    IMM_B,
    IMM_U,
    IMM_J
  } imm_sel_e;

  typedef struct packed {
    logic [31:0]   instr_data;
    logic [31:0]   instr_mask;
    logic [1:0]    writeback;
    logic [2:0]    use_rs;
    op_sel_e       op_a_mux;
    op_sel_e       op_b_mux;
    op_sel_e       op_c_mux;
    imm_sel_e      imm_a_mux;
    imm_sel_e      imm_b_mux;
    imm_sel_e      imm_c_mux;
  } offl_instr_t;

endpackage
