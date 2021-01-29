// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

module acc_interconnect #(
  // The number of requesters.
  parameter int NumReq             = -1,
  // The number of rsponders.
  parameter int NumResp            = -1,
  // Accelerator Address Width
  parameter int AccAddrWidth       = acc_pkg::AccAddrWidth,
  // ISA bit width.
  parameter unsigned int DataWidth = 32,
  // Request Type.
  parameter type req_t             = logic,
  // Request Payload Type
  parameter type req_chan_t        = logic,
  // Response Type.
  parameter type rsp_t            = logic,
  // Response Payload Type
  parameter type rsp_chan_t        = logic,

  // Insert Pipelne register into request path
  parameter bit RegisterReq        = 0,
  // Insert Pipelne register into rsponse path
  parameter bit RegisterResp       = 0
) (
  input clk_i,
  input rst_ni,

  input req_t [NumReq-1:0] mst_req_i,
  output req_chan_t [NumResp-1:0] slv_req_o,


  input rsp_t [NumResp-1:0] slv_rsp_i,
  output rsp_t [NumResp-1:0] mst_rsp_o
);


  localparam int unsigned IdxWidth       = cf_math_kg::idx_width(NumReq);
  localparam int unsigned IdWidth  = 5 + IdxWidth;

  typedef logic [DataWidth-1:0]    data_t;
  typedef logic [AccAddrWidth-1:0] addr_t;
  typedef logic [IdWidth-1:0]      id_t;

  // idx_t [NumResp-1:0] core_id;
  // req_t [NumResp-1:0] slv_req;

  // offload path
  stream_xbar #  (
    .NumInp      ( NumReq           ),
    .NumOut      ( NumResp          ),
    .DataWidth   ( DataWidth        ),
    .payload_t   ( req_chan_t       ),
    .OutSpillReg ( RegisterReq      )
  ) offload_xbar_i (
    .clk_i   ( clk_i              ),
    .rst_ni  ( rst_ni             ),
    .flush_i ( 1'b0               ),
    .rr_i    ( '0                 ),
    .data_i  ( mst_req_i.q        ),
    .sel_i   ( mst_req_i.q_addr   ),
    .valid_i ( mst_req_i.q_valid  ),
    .ready_o ( mst_rsp_o.q_ready  ),
    .data_o  ( slv_req_o.q        ),
    .idx_o   (                    ),
    .valid_o ( slv_req_o.q_valid  ),
    .ready_i ( slv_rsp_i.q_ready )
  );


  // rsponse path
  stream_xbar #  (
    .NumInp      ( NumResp     ),
    .NumOut      ( NumReq      ),
    .DataWidth   ( DataWidth   ),
    .payload_t   ( rsp_chan_t ),
    .OutSpillReg ( RegisterReq )
  ) offload_xbar_i (
    .clk_i   ( clk_i                       ),
    .rst_ni  ( rst_ni                      ),
    .flush_i ( 1'b0                        ),
    .rr_i    ( '0                          ),
    .data_i  ( slv_rsp_i.p                 ),
    .sel_i   ( slv_rsp_i.p_id[IdWidth-1:5] ),
    .valid_i ( slv_rsp_i.p_valid           ),
    .ready_o ( slv_req_o.p_ready           ),
    .data_o  ( mst_rsp_o                   ),
    .idx_o   (                             ),
    .valid_o ( mst_req_o.q_valid           ),
    .ready_i ( slv_rsp_i.q_ready          )
  );

endmodule



