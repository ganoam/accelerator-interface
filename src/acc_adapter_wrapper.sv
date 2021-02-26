
// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

`include "acc_interface/assign.svh"
`include "acc_interface/typedef.svh"

module acc_adapter_wrapper #(

  parameter int unsigned DataWidth         = 32,
  parameter int          NumHier           = 3,
  parameter int          NumRsp[NumHier]   = '{4,2,2},
  parameter type         acc_req_t         = logic,
  parameter type         acc_req_chan_t    = logic,
  parameter type         acc_rsp_t         = logic,
  parameter type         acc_adapter_req_t = logic,
  parameter type         acc_adapter_rsp_t = logic
) (
  input clk_i,
  input rst_ni,

  input  acc_adapter_req_t adapter_req_i,
  output acc_adapter_rsp_t adapter_rsp_o,

  /*
  // To compressed predecoders
  input  logic [31:0] instr_rdata_if_i,
  output logic [31:0] instr_if_exp_o,
  output logic        instr_if_exp_valid_o,
  */

  output acc_req_t acc_req_o,
  input  acc_rsp_t acc_rsp_i
);
 localparam NumRspTot = acc_pkg::sumn(NumRsp, NumHier);

 logic [31:0] instr_rdata_id;
 acc_pkg::offl_instr_t [NumRspTot-1:0] offload_instr;
 logic [NumRspTot-1:0] offload_accept;

  acc_adapter #(
    .DataWidth         ( DataWidth         ),
    .NumHier           ( NumHier           ),
    .NumRsp            ( NumRsp            ),
    .acc_req_t         ( acc_req_t         ),
    .acc_req_chan_t    ( acc_req_chan_t    ),
    .acc_rsp_t         ( acc_rsp_t         ),
    .acc_adapter_req_t ( acc_adapter_req_t ),
    .acc_adapter_rsp_t ( acc_adapter_rsp_t )
  ) acc_adapter_i (
    .clk_i            ( clk_i          ),
    .rst_ni           ( rst_ni         ),
    .adapter_req_i    ( adapter_req_i  ),
    .adapter_rsp_o    ( adapter_rsp_o  ),
    .offload_instr_i  ( offload_instr  ),
    .offload_accept_i ( offload_accept ),
    .instr_rdata_id_o ( instr_rdata_id ),
    .acc_req_o        ( acc_req_o      ),
    .acc_rsp_i        ( acc_rsp_i      )
  );

  `define dummy_instr_set(acc_num) \

  // Test dummy instructions are defined as follows
  // |  3                   2                   1
  // |1 0 9 8 7 6 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0|
  // |===============================================================|
  // | Acceler | Random Data | W | use |  C  |  B  |  A  | C | B | A |
  // | Number  |             | B | rs  |  Immediate  Mux |   OP MUX  |
  // instr_dak
  `define dummy_instr_(acc_num


endmodule
