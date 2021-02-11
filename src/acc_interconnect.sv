// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

`include "acc_interface/assign.svh"

module acc_interconnect #(
  // The number of requesters.
  parameter int NumReq             = -1,
  // The number of rsponders.
  parameter int NumRsp             = -1,
  // Accelerator Address Width
  parameter int AccAddrWidth       = acc_pkg::AccAddrWidth,
  // ISA bit width.
  parameter int unsigned DataWidth = 32,
  // ID Width at the request master side
  // The ID width at the output will be InIdWidth + clog2(NumReq) (localparam)
  parameter int InIdWidth          = -1,
  // Due to different widths of the ID field at the request master and slave
  // side, we need separate struct typedefs.
  // Master Request Type.
  parameter type mst_req_t         = logic,
  // Master Request Payload Type
  parameter type mst_req_chan_t    = logic,
  // Slave Request Type.
  parameter type slv_req_t         = logic,
  // Slave Request Payload Type
  parameter type slv_req_chan_t    = logic,
  // Response Type.
  parameter type rsp_t             = logic,
  // Response Payload Type
  parameter type rsp_chan_t        = logic,

  // Insert Pipeline register into request path
  parameter bit RegisterReq        = 0,
  // Insert Pipeline register into rsponse path
  parameter bit RegisterRsp        = 0
) (
  input clk_i,
  input rst_ni,

  input  mst_req_t [NumReq-1:0] mst_req_i,
  output rsp_t [NumReq-1:0]     mst_rsp_o,

  output slv_req_t [NumRsp-1:0] slv_req_o,
  input  rsp_t [NumRsp-1:0]     slv_rsp_i
);

  localparam int unsigned IdxWidth = cf_math_pkg::idx_width(NumReq);
  localparam int unsigned IdWidth  = InIdWidth + IdxWidth;

  typedef logic [AccAddrWidth-1:0] addr_t;


  mst_req_chan_t [NumReq-1:0] mst_req_q_chan;
  addr_t         [NumReq-1:0] mst_req_q_addr;
  logic          [NumReq-1:0] mst_req_q_valid;
  logic          [NumReq-1:0] mst_req_p_ready;

  // this is mst_req_t, bc the payload does not change through the crossbar.
  mst_req_chan_t [NumRsp-1:0] slv_req_q_chan;
  logic          [NumRsp-1:0] slv_req_q_valid;
  logic          [NumRsp-1:0] slv_req_p_ready;

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

  for (genvar i=0; i<NumRsp; i++) begin : gen_slv_req_assignment
    // Assign payload signals
    `ACC_ASSIGN_Q_SIGNALS(assign, slv_req_o[i].q, slv_req_q_chan[i], "id", {sender_id[i], slv_req_q_chan[i].id})
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
    .payload_t   ( mst_req_chan_t       ),
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


  // response path
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
  // ID Width at the request master side
  // The ID width at the output will be InIdWidth + clog2(NumReq) (localparam)
  parameter int InIdWidth          = -1,
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

  localparam int unsigned IdxWidth    = cf_math_pkg::idx_width(NumReq);
  localparam int unsigned ExtIdWidth  = InIdWidth + IdxWidth;

  typedef logic [DataWidth-1:0]    data_t;
  typedef logic [AccAddrWidth-1:0] addr_t;
  typedef logic [InIdWidth-1:0]    in_id_t;
  typedef logic [ExtIdWidth-1:0]   ext_id_t;

  // This generates some unused typedefs. still cleaner than invoking macros
  // separately.
  `ACC_TYPEDEF_ALL(acc_mst, addr_t, data_t, in_id_t)
  `ACC_TYPEDEF_ALL(acc_slv, addr_t, data_t, ext_id_t)

  acc_mst_req_t [NumReq-1:0] acc_mst_req;
  acc_slv_rsp_t [NumReq-1:0] acc_mst_rsp;

  acc_slv_req_t [NumRsp-1:0] acc_slv_req;
  acc_slv_rsp_t [NumRsp-1:0] acc_slv_rsp;

  acc_interconnect #(
    .NumReq         ( NumReq             ),
    .NumRsp         ( NumRsp             ),
    .AccAddrWidth   ( AccAddrWidth       ),
    .DataWidth      ( DataWidth          ),
    .InIdWidth      ( InIdWidth          ),
    .mst_req_t      ( acc_mst_req_t      ),
    .mst_req_chan_t ( acc_mst_req_chan_t ),
    .slv_req_t      ( acc_slv_req_t      ),
    .slv_req_chan_t ( acc_slv_req_chan_t ),
    .rsp_t          ( acc_slv_rsp_t      ),
    .rsp_chan_t     ( acc_slv_rsp_chan_t ),
    .RegisterReq    ( RegisterReq        ),
    .RegisterRsp    ( RegisterRsp        )
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

