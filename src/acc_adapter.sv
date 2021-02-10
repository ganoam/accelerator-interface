// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

`include "acc_interface/assign.svh"
`include "acc_interface/typedef.svh"

module acc_adapter #(
  parameter int unsigned DataWidth       = 32,
  parameter int          NumHier         = 3,
  parameter int          NumRsp[NumHier] = '{4,2,2},
  parameter int          NumRspTot       =-1,
  parameter type         acc_req_t       = logic,
  parameter type         acc_req_chan_t  = logic,
  parameter type         acc_rsp_t       = logic
) (
  input clk_i,
  input rst_ni,

  input logic [31:0]          instr_rdata_id_i,
  input logic [DataWidth-1:0] rs1_i,
  input logic [DataWidth-1:0] rs2_i,
  input logic [DataWidth-1:0] rs3_i,
  input logic [2:0]           rs_valid_i,

  input logic  [31:0] instr_rdata_if_i,
  output logic [31:0] instr_if_exp,
  output logic        instr_if_exp_valid_o,

  input logic        offload_valid_i,
  output logic       offload_ready_o,
  output logic       offload_accept_o,
  output logic [1:0] offload_writeback_o,

  output acc_req_t acc_req_o,
  input  acc_rsp_t acc_rsp_i
);

  import acc_pkg::*;
  localparam HierAddrWidth = cf_math_pkg::idx_width(NumHier);
  localparam MaxNumRsp     = maxn(NumRsp, NumHier);
  localparam AccAddrWidth  = cf_math_pkg::idx_width(MaxNumRsp);

  localparam AddrWidth = HierAddrWidth + AccAddrWidth;

  // Request state
  logic acc_out_ready;
  logic acc_out_valid;
  acc_req_chan_t acc_out_req;

  logic [4:0] instr_rd;

  logic [31:0] imm_i_type;
  logic [31:0] imm_s_type;
  logic [31:0] imm_b_type;
  logic [31:0] imm_u_type;
  logic [31:0] imm_j_type;

  logic [31:0] op_a_imm;
  logic [31:0] op_b_imm;
  logic [31:0] op_c_imm;

  imm_sel_e [NumRspTot-1:0] op_a_imm_mux;
  imm_sel_e [NumRspTot-1:0] op_b_imm_mux;
  imm_sel_e [NumRspTot-1:0] op_c_imm_mux;

  op_sel_e [NumRspTot-1:0] op_a_mux;
  op_sel_e [NumRspTot-1:0] op_b_mux;
  op_sel_e [NumRspTot-1:0] op_c_mux;

  logic [NumRspTot-1:0]       offload_accept;
  logic [1:0] [NumRspTot-1:0] offload_writeback;
  logic [2:0] [NumRspTot-1:0] offload_use_rs;
  logic [2:0] use_rs;

  // Destination register
  assign instr_rd = instr_rdata_id_i[11:7];

  // Immediate extraction and sign extension
  assign imm_i_type = { {20{instr_rdata_id_i[31]}}, instr_rdata_id_i[31:20] };
  assign imm_s_type =
    { {20{instr_rdata_id_i[31]}}, instr_rdata_id_i[31:25], instr_rdata_id_i[11:7] };
  assign imm_b_type =
    { {19{instr_rdata_id_i[31]}}, instr_rdata_id_i[31], instr_rdata_id_i[7],
          instr_rdata_id_i[30:25], instr_rdata_id_i[11:8], 1'b0 };
  assign imm_u_type = { instr_rdata_id_i[31:12], 12'b0 };
  assign imm_j_type =
    { {12{instr_rdata_id_i[31]}}, instr_rdata_id_i[19:12], instr_rdata_id_i[20],
          instr_rdata_id_i[30:21], 1'b0 };

  logic [31:0][NumRspTot-1:0] acc_op_a;
  logic [31:0][NumRspTot-1:0] acc_op_b;
  logic [31:0][NumRspTot-1:0] acc_op_c;

  logic [31:0][NumRspTot-1:0] acc_imm_a;
  logic [31:0][NumRspTot-1:0] acc_imm_b;
  logic [31:0][NumRspTot-1:0] acc_imm_c;

  // operand muxes
  for (genvar i=0; i<NumRspTot; i++) begin : gen_op_mux
    always_comb begin
      acc_op_a[i] = '0;
      acc_op_b[i] = '0;
      acc_op_c[i] = '0;
      unique case (op_a_imm_mux[i])
        IMM_I:   acc_imm_a[i] = imm_i_type;
        IMM_S:   acc_imm_a[i] = imm_s_type;
        IMM_B:   acc_imm_a[i] = imm_b_type;
        IMM_U:   acc_imm_a[i] = imm_u_type;
        IMM_J:   acc_imm_a[i] = imm_j_type;
        default: acc_imm_a[i] = imm_i_type;
      endcase
      unique case (op_b_imm_mux[i])
        IMM_I:   acc_imm_b[i] = imm_i_type;
        IMM_S:   acc_imm_b[i] = imm_s_type;
        IMM_B:   acc_imm_b[i] = imm_b_type;
        IMM_U:   acc_imm_b[i] = imm_u_type;
        IMM_J:   acc_imm_b[i] = imm_j_type;
        default: acc_imm_b[i] = imm_i_type;
      endcase
      unique case (op_c_imm_mux[i])
        IMM_I:   acc_imm_c[i] = imm_i_type;
        IMM_S:   acc_imm_c[i] = imm_s_type;
        IMM_B:   acc_imm_c[i] = imm_b_type;
        IMM_U:   acc_imm_c[i] = imm_u_type;
        IMM_J:   acc_imm_c[i] = imm_j_type;
        default: acc_imm_c[i] = imm_i_type;
      endcase
      if (offload_accept[i]) begin
        acc_op_a[i] = op_a_mux[i] == OP_RS ? rs1_i : acc_imm_a[i];
        acc_op_b[i] = op_b_mux[i] == OP_RS ? rs1_i : acc_imm_b[i];
        acc_op_c[i] = op_c_mux[i] == OP_RS ? rs1_i : acc_imm_c[i];
      end
    end
  end

  // Determine address:
  // The first NumRsp[0] requests go to level 0
  // The next NumRsp[1] requests go to level 1
  // ...
  logic [NumHier-1:0] hier_onehot;
  logic [HierAddrWidth-1:0] hier_addr;
  logic [AccAddrWidth-1:0][NumHier-1:0] acc_addr;
  logic [MaxNumRsp-1:0][NumHier-1:0] offload_accept_lvl;
  for (genvar i=0; i<NumHier; i++) begin : gen_acc_addr
    localparam SumNumRsp = i == 0 ? 0 : sumn(NumRsp, i-1);
    logic [NumRspTot-1:0] shift_offload_accept;
    assign shift_offload_accept = offload_accept >> SumNumRsp;
    assign offload_accept_lvl[i] = {{MaxNumRsp-NumRsp[i]{1'b0}}, shift_offload_accept[NumRsp[i]-1:0]};
    assign hier_onehot[i] = |offload_accept_lvl[NumRsp[i]-1:0];
    onehot_to_bin #(
      .ONEHOT_WIDTH(MaxNumRsp )
    ) acc_addr_enc_i (
      .onehot(offload_accept_lvl[i]),
      .bin(acc_addr[i])
    );
  end

  onehot_to_bin #(
    .ONEHOT_WIDTH(NumHier)
  ) hier_addr_enc_i (
    .onehot(hier_onehot),
    .bin(hier_addr)
  );

  // Assemble accelerator request
  always_comb begin
    acc_out_req.data_arga ='0;
    acc_out_req.data_argb ='0;
    acc_out_req.data_argc ='0;
    use_rs                = '0;
    for (int unsigned i=0; i<NumRspTot; i++) begin
      acc_out_req.data_arga |= acc_op_a[i];
      acc_out_req.data_argb |= acc_op_b[i];
      acc_out_req.data_argc |= acc_op_c[i];
      use_rs                |= offload_use_rs[i];
    end
  end
  assign acc_out_req.data_op   = instr_rdata_id_i;
  assign acc_out_req.id        = instr_rd;
  always_comb begin
    acc_out_req.addr[AccAddrWidth-1:0] = '0;
    for (int unsigned i=0; i<NumHier; i++) begin
      acc_out_req.addr[AccAddrWidth-1:0] |= acc_addr;
    end
  end
  assign acc_out_req.addr[AddrWidth-1:AccAddrWidth] = hier_addr;

  // Flow Control
  assign offload_accept_o = |offload_accept;
  assign acc_out_valid    = offload_valid_i && (use_rs^rs_valid_i == '0);
  assign offload_ready_o  = ~offload_accept_o || ((use_rs^rs_valid_i=='0) && acc_out_ready);

  // Instantiate pre-decoders
  acc_predecoder #(
    .instr_t    ( offl_instr_t ),
    .NumInstr   ( 1 ),
    .offl_instr ( '{1}         )
  ) dummy_pred_a_i (
    .instr_rdata_i    ( instr_rdata_id_i     ),
    .offl_accept_o    ( offload_accept[0]    ),
    .offl_writeback_o ( offload_writeback[0] ),
    .offl_use_rs_o    ( offload_use_rs[0]    ),
    .offl_op_a_mux_o  ( op_a_mux[0]          ),
    .offl_op_b_mux_o  ( op_b_mux[0]          ),
    .offl_op_c_mux_o  ( op_c_mux[0]          ),
    .offl_imm_a_mux_o ( op_a_imm_mux[0]      ),
    .offl_imm_b_mux_o ( op_b_imm_mux[0]      ),
    .offl_imm_c_mux_b ( op_c_imm_mux[0]      )
  );

  acc_predecoder #(
    .instr_t    ( offl_instr_t ),
    .NumInstr   ( 1         ),
    .offl_instr ( '{1}         )
  ) dummy_pred_b_i (

    .instr_rdata_i    ( instr_rdata_id_i     ),
    .offl_accept_o    ( offload_accept[1]    ),
    .offl_writeback_o ( offload_writeback[1] ),
    .offl_use_rs_o    ( offload_use_rs[1]    ),
    .offl_op_a_mux_o  ( op_a_mux[1]          ),
    .offl_op_b_mux_o  ( op_b_mux[1]          ),
    .offl_op_c_mux_o  ( op_c_mux[1]          ),
    .offl_imm_a_mux_o ( op_a_imm_mux[1]      ),
    .offl_imm_b_mux_o ( op_b_imm_mux[1]      ),
    .offl_imm_c_mux_b ( op_c_imm_mux[1]      )
  );

  // To acc interconnect.
  stream_fifo#(
    .FALL_THROUGH ( 1'b1       ),
    .DEPTH        ( 1          ),
    .T            ( acc_req_chan_t )
  ) acc_req_out_reg (
    .clk_i   ( clk_i             ),
    .rst_ni  ( rst_ni            ),
    .clr_i   ( 1'b0              ),
    .valid_i ( acc_out_valid     ),
    .ready_o ( acc_out_ready     ),
    .data_i  ( acc_out_req       ),
    .valid_o ( acc_req_o.q_valid ),
    .ready_i ( acc_rsp_i.q_ready ),
    .data_o  ( acc_req_o.q       )
  );

  // Sanity Checks
  assert property (@(posedge clk_i) $onehot0(offload_accept)) else
      $error("Multiple accelerators accepeting request");
  assert property (@(posedge clk_i) (offload_valid_i && !offload_ready_o)
                   |=> $stable(instr_rdata_id_i)) else
      $error ("instr_rdata_id_i is unstable");
  assert property (@(posedge clk_i) (offload_valid_i && !offload_ready_o) |=> offload_valid_i) else
      $error("offload_valid_i has been taken away without a ready");
  assert property (@(posedge clk_i) (offload_valid_i && offload_ready_o && offload_accept_o)
                   |-> (rs_valid_i ^ use_rs) == '0) else
      $error("accepted offload request with invalid source registers");



endmodule
