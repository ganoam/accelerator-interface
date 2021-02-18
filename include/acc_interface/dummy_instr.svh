// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Noam Gallmann <gnoam@live.com>

// Accelerator Adapter Dummy Instruction definition macros
`ifndef ACC_DUMMY_INSTR_SVH_
`define ACC_DUMMY_INSTR_SVH_


// Dummy instructions are encoded as follows
// |  3                   2                   1
// |1 0 9 8 7 6 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0|
// |===============================================================|
// | f7          | rs2     | rs1     | f3  | rd      | opcode  |1 1| R-type
// | rs3     | f2| rs2     | rs1     | f3  | rd      | opcode  |1 1| R4-type
// | imm-I                 | rs1     | f3  | rd      | opcode  |1 1| I-type
// | imm-S       | rs2     | rs1     | f3  | imm-S   | opcode  |1 1| S-type
// | imm-B       | rs2     | rs1     | f3  | imm-B   | opcode  |1 1| B-type
// | h
// |
// |
// |
// |
// |                                                 | Type    |1 1|
//
// | Acceler | Random Data | W | use |  C  |  B  |  A  | C | B | A |
// | Number  |             | B | rs  |  Immediate  Mux |   OP MUX  |
//
// For every predecoder implemented in the test, we define
// T

`define DUMMY_INSTR( use_rs, acc_num,


import acc_pkg::*;

`endif // ACC_DUMMY_INSTR_SVH_


