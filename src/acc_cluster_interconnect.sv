// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

`include "acc_interface/assign.svh"

module acc_interconnect #(
  // Global Number of Hierarchy Levels
  parameter int NumHier            = -1,
  // The number of requesters per level.
  parameter int NumReq[NumHier]    = {-1},
  // The number of rsponders per level.
  parameter int NumRsp[NumHier]    = {-1},
  // Global Number of Hierarchy Levels
  parameter int NumHier            = -1,
  // Hierarchy level
  parameter int HierLevel          = -1,
  // ISA bit width.
  parameter int unsigned DataWidth = 32,
  // Insert Pipeline register into request path
  parameter bit RegisterReq        = 0,
  // Insert Pipeline register into rsponse path
  parameter bit RegisterRsp        = 0,
  // Accelerator Address Width
  parameter int AccAddrWidth       = -1

  // Due to different widths of the ID field at the request master and slave
  // side, we need separate struct typedefs.
  // Standard types feature an Id signal of width 5.
  // Extended types feature an Id signal of width 5+idx_width(NumReq).
  // Std Request Type : IdWidth = 5
  parameter type req_t          = logic,
  // Std Request Payload Type
  parameter type req_chan_t     = logic,
  // Std Response Type.
  parameter type rsp_t          = logic,
  // Std Response Payload Type.
  parameter type rsp_chan_t     = logic,
  // Extended Request Type.
  parameter type ext_req_t      = logic,
  // Extended Request Payload Type
  parameter type ext_req_chan_t = logic,
  // Extended Response Type
  parameter type ext_rsp_t      = logic,
  // Extended Response Payload Type
  parameter type ext_rsp_chan_t = logic
) (
  input clk_i,
  input rst_ni,

  // From / To requesting entity
  input  req_t [NumReq-1:0] mst_req_i,
  output rsp_t [NumReq-1:0] mst_rsp_o,

  // From / To next cluster level
  output req_t [NumReq-1:0] mst_req_o,
  input  rsp_t [NumReq-1:0] mst_rsp_i,

  // From / To responding entity
  output ext_req_t [NumRsp-1:0] slv_req_o,
  input  ext_rsp_t [NumRsp-1:0] slv_rsp_i
);

  localparam int unsigned IdxWidth   = cf_math_pkg::idx_width(NumReq);
  localparam int unsigned ExtIdWidth = 5 + IdxWidth;

  localparam logic [$cf_math_pkg::idx_width(NumHier)-1:0] HierAddr = HierLevel;

  typedef logic [AccAddrWidth-1:0] addr_t;


  req_chan_t [NumReq-1:0]         mst_req_q_chan;
  addr_t     [NumReq-1:0]         mst_req_q_addr;
  logic      [NumReq-1:0]         mst_req_q_valid;
  logic      [NumReq-1:0]         mst_req_p_ready;
  // Hierarchy level address
  logic      [NumReq-1:0] [cf_math_pkg::idx_width(NumHier)-1:0] mst_req_q_level;


  // this is mst_req_t, bc the payload does not change through the crossbar.
  req_chan_t [NumRsp-1:0] slv_req_q_chan;
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
    // Hierarchy level address
    assign mst_req_q_level[i] =
      mst_req_i[i].q.addr[AccAddrWidth-1:AccAddrWidth-cf_math_pkg::idx_width(NumHier)-1];
    // hang in bypass signals
    // assign mst_req_q_valid[i] = mst_req_i[i].q_valid;
    //assign mst_req_p_ready[i] = mst_req_i[i].p_ready;
  end

  for (genvar i=0; i<NumRsp; i++) begin : gen_slv_req_assignment
    // Extend ID signal at slave side
    `ACC_ASSIGN_Q_SIGNALS(assign, slv_req_o[i].q, slv_req_q_chan[i], "id", {sender_id[i], slv_req_q_chan[i].id})
    assign slv_req_o[i].q_valid     = slv_req_q_valid[i];
    assign slv_req_o[i].p_ready     = slv_req_p_ready[i];
  end

  for (genvar i=0; i<NumRsp; i++) begin : gen_mst_rsp_assignment
    // Discard upper bits of ID signal after xbar traversal.
    `ACC_ASSIGN_P_SIGNALS(assign, slv_rsp_p_chan[i], slv_rsp_i[i].p, "id", slv_rsp_i[i].p.id[4:0])
    assign receiver_id[i]     = slv_rsp_i[i].p.id[ExtIdWidth-1:5];
    assign slv_rsp_p_valid[i] = slv_rsp_i[i].p_valid;
    assign slv_rsp_q_ready[i] = slv_rsp_i[i].q_ready;
  end

  for (genvar i=0; i<NumReq; i++) begin : gen_slv_rsp_assignment
    assign mst_rsp_o[i].p       = mst_rsp_p_chan[i];
    // hang in bypass signals
    // assign mst_rsp_o[i].p_valid = mst_rsp_p_valid[i];
    // assign mst_rsp_o[i].q_ready = mst_rsp_q_ready[i];
  end

  // Bypass this hierarchy level
  if ( NumHier-1 > HierLevel ) begin : gen_bypass_interconnect
    for ( genvar i=0; i<NumReq; i++ ) begin : gen_offload_bypass_demux
      stream_demux #(
        .N_OUP ( 2 )
      ) offload_bypass_demux_i (
        .inp_valid_i ( mst_req_i[i].q_valid                    ),
        .inp_ready_o ( mst_rsp_o[i].q_ready                    ),
        .oup_sel_i   ( mst_req_q_level[i] == HierAddr          ),
        .oup_valid_o ( {mst_req_o[i].q_valid, mst_req_q_valid[i]} ),
        .oup_ready_i ( {mst_rsp_i[i].q_ready, mst_rsp_q_ready[i]} )
      );

      stream_arbiter #(
        .DATA_T  ( rsp_t ),
        .N_INP   ( 2     ),
        .ARBITER ( "rr"  )
      ) response_bypass_arbiter_i (
        .clk_i       ( clk_i                                      ),
        .rst_ni      ( rst_ni                                     ),
        .inp_data_i  ( {mst_rsp_i[i].p, mst_rsp_p_chan[i]}        ),
        .inp_valid_i ( {mst_rsp_i[i].p_valid, mst_rsp_p_valid[i]} ),
        .inp_ready_o ( {mst_req_o[i].p_ready, mst_req_p_ready[i]} ),
        .oup_data_o  ( mst_rsp_o[i].p                             ),
        .oup_valid_o ( mst_rsp_o[i].p_valid                       ),
        .oup_ready_i ( mst_req_i[i].p_ready                       )
      );
    end
  end else begin : gen_no_bypass_interconnect
    logic      [NumReq-1:0] unused_mst_rsp_q_ready;
    rsp_chan_t [NumReq-1:0] unused_mst_rsp_p;
    logic      [NumReq-1:0] unused_mst_rsp_p_valid;

    for ( genvar i=0; i<NumReq; i++ ) begin : gen_offload_bypass_demux
      // Direct assignments
      // Offload path
      assign mst_req_q_valid[i]   = mst_req_i[i].q_valid;
      assign mst_rsp_o[i].q_ready = mst_rsp_q_ready[i];
      // Request path
      assign mst_rsp_o[i].p_valid = mst_rsp_p_valid[i];
      assign mst_req_p_ready[i]   = mst_req_i[i].p_ready;

      // Tie off unused signals
      assign mst_req_o[i].q            = '0;
      assign mst_req_o[i].q_valid      = 1'b0;
      assign unused_mst_rsp_q_ready[i] = mst_rsp_i[i].q_ready;

      assign unused_mst_rsp_p[i]       = mst_rsp_i[i].p;
      assign unused_mst_rsp_p_valid[i] = mst_rsp_i[i].p_valid;
      assign mst_req_o[i].p_ready      = 1'b0;
    end
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
  // Insert Pipelne register into request path
  parameter bit RegisterReq        = 0,
  // Insert Pipelne register into rsponse path
  parameter bit RegisterRsp        = 0
) (
  input clk_i,
  input rst_ni,

  ACC_BUS mst       [NumReq],
  ACC_BUS mst_next  [NumReq],
  ACC_BUS slv       [NumRsp]
);

  localparam int unsigned IdxWidth    = cf_math_pkg::idx_width(NumReq);
  localparam int unsigned ExtIdWidth  = 5 + IdxWidth;

  typedef logic [DataWidth-1:0]    data_t;
  typedef logic [AccAddrWidth-1:0] addr_t;
  typedef logic [4:0]              in_id_t;
  typedef logic [ExtIdWidth-1:0]   ext_id_t;

  // This generates some unused typedefs. still cleaner than invoking macros
  // separately.
  `ACC_TYPEDEF_ALL(acc, addr_t, data_t, in_id_t)
  `ACC_TYPEDEF_ALL(acc_ext, addr_t, data_t, ext_id_t)

  acc_req_t [NumReq-1:0] acc_mst_req;
  acc_rsp_t [NumReq-1:0] acc_mst_rsp;

  acc_req_t [NumReq-1:0] acc_mst_next_req;
  acc_rsp_t [NumReq-1:0] acc_mst_next_rsp;

  acc_ext_req_t [NumRsp-1:0] acc_slv_req;
  acc_ext_rsp_t [NumRsp-1:0] acc_slv_rsp;

  acc_interconnect #(
    .NumReq         ( NumReq             ),
    .NumRsp         ( NumRsp             ),
    .AccAddrWidth   ( AccAddrWidth       ),
    .DataWidth      ( DataWidth          ),
    .RegisterReq    ( RegisterReq        ),
    .RegisterRsp    ( RegisterRsp        ),
    .req_t          ( acc_req_t          ),
    .req_chan_t     ( acc_req_chan_t     ),
    .rsp_t          ( acc_rsp_t          ),
    .rsp_chan_t     ( acc_rsp_chan_t     ),
    .ext_req_t      ( acc_ext_req_t      ),
    .ext_req_chan_t ( acc_ext_req_chan_t ),
    .ext_rsp_t      ( acc_ext_rsp_t      ),
    .ext_rsp_chan_t ( acc_ext_rsp_chan_t )
  ) acc_interconnect_i (
    .clk_i     ( clk_i             ),
    .rst_ni    ( rst_ni            ),
    .mst_req_i ( acc_mst_req       ),
    .mst_rsp_o ( acc_mst_rsp       ),
    .mst_req_o ( acc_mst_next_req ),
    .mst_rsp_i ( acc_mst_next_rsp ),
    .slv_req_o ( acc_slv_req       ),
    .slv_rsp_i ( acc_slv_rsp       )
  );

  for (genvar i=0; i<NumReq; i++) begin : gen_mst_interface_assignement
    `ACC_ASSIGN_TO_REQ(acc_mst_req[i], mst[i])
    `ACC_ASSIGN_FROM_RESP(mst[i], acc_mst_rsp[i])
  end
  for (genvar i=0; i<NumRsp; i++) begin : gen_slv_interface_assignement
    `ACC_ASSIGN_FROM_REQ(slv[i], acc_slv_req[i])
    `ACC_ASSIGN_TO_RESP(acc_slv_rsp[i], slv[i])
  end
  for (genvar i=0; i<NumReq; i++) begin : gen_mst_next_interface_assignement
    `ACC_ASSIGN_FROM_REQ(mst_next[i], acc_mst_next_req[i])
    `ACC_ASSIGN_TO_RESP(acc_mst_next_rsp[i], mst_next[i])
  end

endmodule

