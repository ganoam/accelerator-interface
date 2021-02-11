// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

module acc_interconnect #(
  // The number of requesters.
  parameter int NumReq             = -1,
  // The number of rsponders.
  parameter int NumRsp             = -1,
  // Accelerator Address Width
  parameter int AccAddrWidth       = acc_pkg::AccAddrWidth,
  // ISA bit width.
  parameter int unsigned DataWidth = 32,
  // Request Type.
  parameter type req_t             = logic,
  // Request Payload Type
  parameter type req_chan_t        = logic,
  // Response Type.
  parameter type rsp_t             = logic,
  // Response Payload Type
  parameter type rsp_chan_t        = logic,

  // Insert Pipelne register into request path
  parameter bit RegisterReq        = 0,
  // Insert Pipelne register into rsponse path
  parameter bit RegisterRsp        = 0
) (
  input clk_i,
  input rst_ni,

  // TODO: change back to single id field -> different req_t at slv and master
  // ports.
  input  req_t [NumReq-1:0] mst_req_i,
  output rsp_t [NumReq-1:0] mst_rsp_o,

  output req_t [NumRsp-1:0] slv_req_o,
  input  rsp_t [NumRsp-1:0] slv_rsp_i
);

  localparam int unsigned IdxWidth = cf_math_pkg::idx_width(NumReq);
  localparam int unsigned IdWidth  = 5 + IdxWidth;

  //typedef logic [DataWidth-1:0]    data_t;
  typedef logic [AccAddrWidth-1:0] addr_t;
  typedef logic [IdWidth-1:0]      id_t;


  req_chan_t [NumReq-1:0] mst_req_q_chan;
  addr_t     [NumReq-1:0] mst_req_q_addr;
  logic      [NumReq-1:0] mst_req_q_valid;
  logic      [NumReq-1:0] mst_req_p_ready;

  req_chan_t [NumRsp-1:0] slv_req_q_chan;
  addr_t     [NumRsp-1:0] slv_req_q_addr;
  logic      [NumRsp-1:0] slv_req_q_valid;
  logic      [NumRsp-1:0] slv_req_p_ready;

  logic [NumRsp-1:0][IdxWidth-1:0] sender_id; // assigned by crossbar.
  logic [NumRsp-1:0][IdxWidth-1:0] receiver_id; // assigned by crossbar.

  rsp_chan_t [NumReq-1:0] mst_rsp_p_chan;
  logic      [NumReq-1:0] mst_rsp_p_valid;
  logic      [NumReq-1:0] mst_rsp_q_ready;

  rsp_chan_t [NumRsp-1:0] slv_rsp_p_chan;
  logic      [NumRsp-1:0] slv_rsp_p_valid;
  logic      [NumRsp-1:0] slv_rsp_q_ready;

  for (genvar i=0; i<NumReq; i++) begin : gen_mst_req_assignment
    assign mst_req_q_chan[i]  = mst_req_i[i].q;
    assign mst_req_q_addr[i]  = mst_req_i[i].q.addr;
    assign mst_req_q_valid[i] = mst_req_i[i].q_valid;
    assign mst_req_p_ready[i] = mst_req_i[i].p_ready;
  end

  // TODO: unpacking macro??
  for (genvar i=0; i<NumRsp; i++) begin : gen_slv_req_assignment
    // Assign payload signals
    assign slv_req_o[i].q.data_arga = slv_req_q_chan[i].data_arga;
    assign slv_req_o[i].q.data_argb = slv_req_q_chan[i].data_argb;
    assign slv_req_o[i].q.data_argc = slv_req_q_chan[i].data_argc;
    assign slv_req_o[i].q.data_op   = slv_req_q_chan[i].data_op;
    // Set upper bits of id field.
    assign slv_req_o[i].q.id        = slv_req_q_chan[i].id |  {sender_id[i], 5'b0} ;
    // The Address field is no longer needed.
    assign slv_req_o[i].q_addr      = '0;
    assign slv_req_o[i].q_valid     = slv_req_q_valid[i];
    assign slv_req_o[i].p_ready     = slv_req_p_ready[i];
  end

  for (genvar i=0; i<NumRsp; i++) begin : gen_mst_rsp_assignment
    assign slv_rsp_p_chan[i]  = slv_rsp_i[i].p;
    assign receiver_id[i]     = slv_rsp_i[i].p.id[IdWidth-1:5];
    assign slv_rsp_p_valid[i] = slv_rsp_i[i].p_valid;
    assign slv_rsp_q_ready[i] = slv_rsp_i[i].q_ready;
  end

  for (genvar i=0; i<NumReq; i++) begin : gen_slv_rsp_assignment
    assign mst_rsp_o[i].p       = mst_rsp_p_chan[i];
    assign mst_rsp_o[i].p_valid = mst_rsp_p_valid[i];
    assign mst_rsp_o[i].q_ready = mst_rsp_q_ready[i];
  end

  // offload path
  stream_xbar   #(
    .NumInp      ( NumReq           ),
    .NumOut      ( NumRsp           ),
    .DataWidth   ( DataWidth        ),
    .payload_t   ( req_chan_t       ),
    .OutSpillReg ( RegisterReq      )
  ) offload_xbar_i (
    .clk_i   ( clk_i           ),
    .rst_ni  ( rst_ni          ),
    .flush_i ( 1'b0            ),
    .rr_i    ( '0              ),
    .data_i  ( mst_req_q_chan  ),
    .sel_i   ( mst_req_q_addr  ),
    .valid_i ( mst_req_q_valid ),
    .ready_o ( mst_rsp_q_ready ),
    .data_o  ( slv_req_q_chan  ),
    .idx_o   ( sender_id       ),
    .valid_o ( slv_req_q_valid ),
    .ready_i ( slv_rsp_q_ready )
  );


  // rsponse path
  stream_xbar   #(
    .NumInp      ( NumRsp      ),
    .NumOut      ( NumReq      ),
    .DataWidth   ( DataWidth   ),
    .payload_t   ( rsp_chan_t  ),
    .OutSpillReg ( RegisterReq )
  ) response_xbar_i (
    .clk_i   ( clk_i           ),
    .rst_ni  ( rst_ni          ),
    .flush_i ( 1'b0            ),
    .rr_i    ( '0              ),
    .data_i  ( slv_rsp_p_chan  ),
    .sel_i   ( receiver_id     ),
    .valid_i ( slv_rsp_p_valid ),
    .ready_o ( slv_req_p_ready ),
    .data_o  ( mst_rsp_p_chan  ),
    .idx_o   (                 ),
    .valid_o ( mst_rsp_p_valid ),
    .ready_i ( mst_req_p_ready )
  );

endmodule

`include "acc_interface/typedef.svh"
`include "acc_interface/assign.svh"

module acc_interconnect_intf #(
  // The number of requesters.
  parameter int NumReq             = -1,
  // The number of rsponders.
  parameter int NumRsp             = -1,
  // Accelerator Address Width
  parameter int AccAddrWidth       = acc_pkg::AccAddrWidth,
  // ISA bit width.
  parameter int unsigned DataWidth = 32,
  // Request Type.
  parameter type req_t             = logic,
  // Request Payload Type
  parameter type req_chan_t        = logic,
  // Response Type.
  parameter type rsp_t             = logic,
  // Response Payload Type
  parameter type rsp_chan_t        = logic,

  // Insert Pipelne register into request path
  parameter bit RegisterReq        = 0,
  // Insert Pipelne register into rsponse path
  parameter bit RegisterRsp        = 0
) (
  input clk_i,
  input rst_ni,

  ACC_BUS mst [NumReq],
  ACC_BUS slv [NumRsp]
);

  localparam int unsigned IdxWidth       = cf_math_pkg::idx_width(NumReq);
  localparam int unsigned IdWidth  = 5 + IdxWidth;

  typedef logic [DataWidth-1:0]    data_t;
  typedef logic [AccAddrWidth-1:0] addr_t;
  typedef logic [IdWidth-1:0]      id_t;

  `ACC_TYPEDEF_ALL(acc, addr_t, data_t, id_t)

  acc_req_t [NumRsp-1:0] acc_slv_req;
  acc_rsp_t [NumRsp-1:0] acc_slv_rsp;

  acc_req_t [NumReq-1:0] acc_mst_req;
  acc_rsp_t [NumReq-1:0] acc_mst_rsp;

  acc_interconnect #(
    .NumReq       ( NumReq         ),
    .NumRsp       ( NumRsp         ),
    .AccAddrWidth ( AccAddrWidth   ),
    .DataWidth    ( DataWidth      ),
    .req_t        ( acc_req_t      ),
    .req_chan_t   ( acc_req_chan_t ),
    .rsp_t        ( acc_rsp_t      ),
    .rsp_chan_t   ( acc_rsp_chan_t ),
    .RegisterReq  ( RegisterReq    ),
    .RegisterRsp  ( RegisterRsp    )
  ) acc_interconnect_i (
    .clk_i     ( clk_i       ),
    .rst_ni    ( rst_ni      ),
    .mst_req_i ( acc_mst_req ),
    .mst_rsp_o ( acc_mst_rsp ),
    .slv_req_o ( acc_slv_req ),
    .slv_rsp_i ( acc_slv_rsp )
  );

  for (genvar i=0; i<NumReq; i++) begin : gen_mst_interface_assignement
    `ACC_ASSIGN_TO_REQ(acc_mst_req[i], mst[i])
    `ACC_ASSIGN_FROM_RESP(mst[i], acc_mst_rsp[i])
  end
  for (genvar i=0; i<NumRsp; i++) begin : gen_slv_interface_assignement
    `ACC_ASSIGN_FROM_REQ(slv[i], acc_slv_req[i])
    `ACC_ASSIGN_TO_RESP(acc_slv_rsp[i], slv[i])
  end

endmodule

