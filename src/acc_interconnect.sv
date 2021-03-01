
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

`include "acc_interface/assign.svh"

module acc_interconnect #(
  // ISA bit width.
  parameter int unsigned DataWidth     = 32,
  // Hierarchy Address Portion
  parameter int unsigned HierAddrWidth = -1,
  // Accelerator Address Portion
  parameter int unsigned AccAddrWidth  = -1,
  // Hierarchy level
  parameter int unsigned HierLevel     = -1,
  // The number of requesters.
  parameter int NumReq                 = -1,
  // The number of rsponders.
  parameter int NumRsp                 = -1,
  // Insert Pipeline register into request path
  parameter bit RegisterReq            = 0,
  // Insert Pipeline register into response path
  parameter bit RegisterRsp            = 0,

  // Due to different widths of the ID field at the request master and slave
  // side, we need separate struct typedefs.
  // Standard types feature an Id signal of width 5.
  // Extended types feature an Id signal of width 5+idx_width(NumReq).
  // Std Request Type : IdWidth = 5
  parameter type acc_c_req_t          = logic,
  // Std Request Payload Type
  parameter type acc_c_req_chan_t     = logic,
  // Std Response Type.
  parameter type acc_c_rsp_t          = logic,
  // Std Response Payload Type.
  parameter type acc_c_rsp_chan_t     = logic,
  // Extended Request Type.
  parameter type acc_c_ext_req_t      = logic,
  // Extended Request Payload Type
  parameter type acc_c_ext_req_chan_t = logic,
  // Extended Response Type
  parameter type acc_c_ext_rsp_t      = logic,
  // Extended Response Payload Type
  parameter type acc_c_ext_rsp_chan_t = logic
) (
  input clk_i,
  input rst_ni,

  // From / To requesting entity
  input  acc_c_req_t [NumReq-1:0] acc_c_slv_req_i,
  output acc_c_rsp_t [NumReq-1:0] acc_c_slv_rsp_o,

  // From / To next cluster level
  output acc_c_req_t [NumReq-1:0] acc_c_mst_next_req_o,
  input  acc_c_rsp_t [NumReq-1:0] acc_c_mst_next_rsp_i,

  // From / To responding entity
  output acc_c_ext_req_t [NumRsp-1:0] acc_c_mst_req_o,
  input  acc_c_ext_rsp_t [NumRsp-1:0] acc_c_mst_rsp_i
);

  localparam int unsigned IdxWidth   = cf_math_pkg::idx_width(NumReq);
  localparam int unsigned ExtIdWidth = 1 + IdxWidth;
  localparam int unsigned AddrWidth  = HierAddrWidth + AccAddrWidth;

  // Local xbar select signal width
  localparam int unsigned OfflAddrWidth = cf_math_pkg::idx_width(NumRsp);

  typedef logic [AddrWidth-1:0] addr_t;


  acc_c_req_chan_t [NumReq-1:0]                     mst_req_q_chan;
  logic      [NumReq-1:0][OfflAddrWidth-1:0]  mst_req_q_addr;
  logic      [NumReq-1:0]                     mst_req_q_valid;
  logic      [NumReq-1:0]                     mst_req_p_ready;
  // Hierarchy level address
  logic      [NumReq-1:0] [HierAddrWidth-1:0] mst_req_q_level;

  // this is mst_req_t, bc the payload does not change through the crossbar.
  acc_c_req_chan_t [NumRsp-1:0] slv_req_q_chan;
  logic      [NumRsp-1:0] slv_req_q_valid;
  logic      [NumRsp-1:0] slv_req_p_ready;

  logic [NumRsp-1:0][IdxWidth-1:0] sender_id; // assigned by crossbar.
  logic [NumRsp-1:0][IdxWidth-1:0] receiver_id; // assigned by crossbar.

  acc_c_rsp_chan_t [NumReq-1:0] mst_rsp_p_chan;
  logic      [NumReq-1:0] mst_rsp_p_valid;
  logic      [NumReq-1:0] mst_rsp_q_ready;

  acc_c_rsp_chan_t [NumRsp-1:0] slv_rsp_p_chan;
  logic      [NumRsp-1:0] slv_rsp_p_valid;
  logic      [NumRsp-1:0] slv_rsp_q_ready;

  for (genvar i=0; i<NumReq; i++) begin : gen_mst_req_assignment
    assign mst_req_q_chan[i]  = acc_c_slv_req_i[i].q;
    // Xbar Address
    assign mst_req_q_addr[i]  = acc_c_slv_req_i[i].q.addr[OfflAddrWidth-1:0];
    // Hierarchy level address
    assign mst_req_q_level[i] = acc_c_slv_req_i[i].q.addr[AddrWidth-1:AccAddrWidth];
  end

  for (genvar i=0; i<NumRsp; i++) begin : gen_slv_req_assignment
    // Extend ID signal at slave side
    `ACC_ASSIGN_Q_SIGNALS(assign, acc_c_mst_req_o[i].q, slv_req_q_chan[i], "id", {sender_id[i], 1'b0})
    assign acc_c_mst_req_o[i].q_valid     = slv_req_q_valid[i];
    assign acc_c_mst_req_o[i].p_ready     = slv_req_p_ready[i];
  end

  for (genvar i=0; i<NumRsp; i++) begin : gen_mst_rsp_assignment
    // Discard upper bits of ID signal after xbar traversal.
    `ACC_ASSIGN_P_SIGNALS(assign, slv_rsp_p_chan[i], acc_c_mst_rsp_i[i].p, "id", 1'b0)
    assign receiver_id[i]     = acc_c_mst_rsp_i[i].p.id[ExtIdWidth-1:1];
    assign slv_rsp_p_valid[i] = acc_c_mst_rsp_i[i].p_valid;
    assign slv_rsp_q_ready[i] = acc_c_mst_rsp_i[i].q_ready;
  end

  // Bypass this hierarchy level
  for ( genvar i=0; i<NumReq; i++ ) begin : gen_bypass_path
    // Offload path
    assign acc_c_mst_next_req_o[i].q = acc_c_slv_req_i[i].q;
    stream_demux #(
      .N_OUP ( 2 )
    ) offload_bypass_demux_i (
      .inp_valid_i ( acc_c_slv_req_i[i].q_valid                       ),
      .inp_ready_o ( acc_c_slv_rsp_o[i].q_ready                       ),
      .oup_sel_i   ( mst_req_q_level[i] != HierLevel            ),
      .oup_valid_o ( {acc_c_mst_next_req_o[i].q_valid, mst_req_q_valid[i]} ),
      .oup_ready_i ( {acc_c_mst_next_rsp_i[i].q_ready, mst_rsp_q_ready[i]} )
    );

    // Response Path
    stream_arbiter #(
      .DATA_T  ( acc_c_rsp_chan_t ),
      .N_INP   ( 2     ),
      .ARBITER ( "rr"  )
    ) response_bypass_arbiter_i (
      .clk_i       ( clk_i                                      ),
      .rst_ni      ( rst_ni                                     ),
      .inp_data_i  ( {acc_c_mst_next_rsp_i[i].p, mst_rsp_p_chan[i]}        ),
      .inp_valid_i ( {acc_c_mst_next_rsp_i[i].p_valid, mst_rsp_p_valid[i]} ),
      .inp_ready_o ( {acc_c_mst_next_req_o[i].p_ready, mst_req_p_ready[i]} ),
      .oup_data_o  ( acc_c_slv_rsp_o[i].p                             ),
      .oup_valid_o ( acc_c_slv_rsp_o[i].p_valid                       ),
      .oup_ready_i ( acc_c_slv_req_i[i].p_ready                       )
    );
  end

  // offload path Xbar
  stream_xbar   #(
    .NumInp      ( NumReq           ),
    .NumOut      ( NumRsp           ),
    .DataWidth   ( DataWidth        ),
    .payload_t   ( acc_c_req_chan_t       ),
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

  // response path Xbar
  stream_xbar   #(
    .NumInp      ( NumRsp      ),
    .NumOut      ( NumReq      ),
    .DataWidth   ( DataWidth   ),
    .payload_t   ( acc_c_rsp_chan_t  ),
    .OutSpillReg ( RegisterRsp )
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
  // ISA bit width.
  parameter int unsigned DataWidth     = 32,
  // Hierarchy Address Portion
  parameter int unsigned HierAddrWidth = -1,
  // Accelerator Address Portion
  parameter int unsigned AccAddrWidth  = -1,
  // Hierarchy level
  parameter int unsigned HierLevel     = -1,
  // The number of requesters
  parameter int NumReq                 = -1,
  // The number of rsponders.
  parameter int NumRsp                 = -1,
  // Insert Pipeline register into request path
  parameter bit RegisterReq            = 0,
  // Insert Pipeline register into response path
  parameter bit RegisterRsp            = 0
) (
  input clk_i,
  input rst_ni,

  ACC_BUS acc_c_slv       [NumReq],
  ACC_BUS acc_c_mst_next  [NumReq],
  ACC_BUS acc_c_mst       [NumRsp]
);

  localparam int unsigned IdxWidth   = cf_math_pkg::idx_width(NumReq);
  localparam int unsigned ExtIdWidth = 1 + IdxWidth;
  localparam int unsigned AddrWidth  = HierAddrWidth + AccAddrWidth;

  typedef logic [DataWidth-1:0]  data_t;
  typedef logic [AddrWidth-1:0]  addr_t;
  typedef logic                  in_id_t;
  typedef logic [ExtIdWidth-1:0] ext_id_t;

  // This generates some unused typedefs. still cleaner than invoking macros
  // separately.
  `ACC_TYPEDEF_ALL(acc_c, addr_t, data_t, in_id_t)
  `ACC_TYPEDEF_ALL(acc_c_ext, addr_t, data_t, ext_id_t)

  acc_c_req_t [NumReq-1:0] acc_c_slv_req;
  acc_c_rsp_t [NumReq-1:0] acc_c_slv_rsp;

  acc_c_req_t [NumReq-1:0] acc_c_mst_next_req;
  acc_c_rsp_t [NumReq-1:0] acc_c_mst_next_rsp;

  acc_c_ext_req_t [NumRsp-1:0] acc_c_mst_req;
  acc_c_ext_rsp_t [NumRsp-1:0] acc_c_mst_rsp;

  acc_interconnect #(
    .DataWidth      ( DataWidth          ),
    .HierAddrWidth  ( HierAddrWidth      ),
    .AccAddrWidth   ( AccAddrWidth       ),
    .HierLevel      ( HierLevel          ),
    .NumReq         ( NumReq             ),
    .NumRsp         ( NumRsp             ),
    .RegisterReq    ( RegisterReq        ),
    .RegisterRsp    ( RegisterRsp        ),
    .acc_c_req_t          ( acc_c_req_t          ),
    .acc_c_req_chan_t     ( acc_c_req_chan_t     ),
    .acc_c_rsp_t          ( acc_c_rsp_t          ),
    .acc_c_rsp_chan_t     ( acc_c_rsp_chan_t     ),
    .acc_c_ext_req_t      ( acc_c_ext_req_t      ),
    .acc_c_ext_req_chan_t ( acc_c_ext_req_chan_t ),
    .acc_c_ext_rsp_t      ( acc_c_ext_rsp_t      ),
    .acc_c_ext_rsp_chan_t ( acc_c_ext_rsp_chan_t )
  ) acc_interconnect_i (
    .clk_i                ( clk_i              ),
    .rst_ni               ( rst_ni             ),
    .acc_c_slv_req_i      ( acc_c_slv_req      ),
    .acc_c_slv_rsp_o      ( acc_c_slv_rsp      ),
    .acc_c_mst_next_req_o ( acc_c_mst_next_req ),
    .acc_c_mst_next_rsp_i ( acc_c_mst_next_rsp ),
    .acc_c_mst_req_o      ( acc_c_mst_req      ),
    .acc_c_mst_rsp_i      ( acc_c_mst_rsp      )
  );

  for (genvar i=0; i<NumReq; i++) begin : gen_slv_interface_assignement
    `ACC_ASSIGN_TO_REQ(acc_c_slv_req[i], acc_c_slv[i])
    `ACC_ASSIGN_FROM_RESP(acc_c_slv[i], acc_c_slv_rsp[i])
  end
  for (genvar i=0; i<NumRsp; i++) begin : gen_mst_interface_assignement
    `ACC_ASSIGN_FROM_REQ(acc_c_mst[i], acc_c_mst_req[i])
    `ACC_ASSIGN_TO_RESP(acc_c_mst_rsp[i], acc_c_mst[i])
  end
  for (genvar i=0; i<NumReq; i++) begin : gen_mst_next_interface_assignement
    `ACC_ASSIGN_FROM_REQ(acc_c_mst_next[i], acc_c_mst_next_req[i])
    `ACC_ASSIGN_TO_RESP(acc_c_mst_next_rsp[i], acc_c_mst_next[i])
  end

endmodule

