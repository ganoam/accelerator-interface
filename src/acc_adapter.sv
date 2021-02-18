// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

`include "acc_interface/assign.svh"
`include "acc_interface/typedef.svh"

module acc_adapter #(
  parameter int unsigned DataWidth         = 32,
  parameter int          NumHier           = 3,
  parameter int          NumRsp[NumHier]   = '{4,2,2},
  parameter type         acc_req_t         = logic,
  parameter type         acc_req_chan_t    = logic,
  parameter type         acc_rsp_t         = logic,
  parameter type         acc_adapter_req_t = logic,
  parameter type         acc_adapter_rsp_t = logic,
  // Dependent parameter DO NOT OVERRIDE
  parameter int NumRspTot                  = acc_pkg::sumn(NumRsp, NumHier)
) (
  input clk_i,
  input rst_ni,

  input  acc_adapter_req_t adapter_req_i,
  output acc_adapter_rsp_t adapter_rsp_o,

  output acc_req_t acc_req_o,
  input  acc_rsp_t acc_rsp_i,

  // To predecoders
  output logic [31:0]                         instr_rdata_id_o,
  input logic [NumRspTot-1:0]                 offload_accept_i,
  input acc_pkg::offl_instr_t [NumRspTot-1:0] offload_instr_i

  /*
  // To compressed predecoders
  input  logic [31:0] instr_rdata_if_i,
  output logic [31:0] instr_if_exp_o,
  output logic        instr_if_exp_valid_o,
  */


);

  /*
  // TODO: Compressed Decoders
  logic [31:0] unused_instr_rdata_if_i;
  assign unused_instr_rdata_if_i = instr_rdata_if_i;
  assign instr_if_exp_valid_o = 1'b0;
  assign instr_if_exp_o = '0;
  */

  import acc_pkg::*;
  localparam MaxNumRsp     = maxn(NumRsp, NumHier);
  localparam HierAddrWidth = cf_math_pkg::idx_width(NumHier);
  localparam AccAddrWidth  = cf_math_pkg::idx_width(MaxNumRsp);
  localparam AddrWidth     = HierAddrWidth + AccAddrWidth;

  logic [31:0] instr_rdata_id;

  logic          acc_out_fifo_ready;
  logic          acc_out_fifo_valid;
  acc_req_chan_t acc_out_fifo_req;

  logic [4:0] instr_rd;

  logic [31:0] imm_i_type;
  logic [31:0] imm_s_type;
  logic [31:0] imm_b_type;
  logic [31:0] imm_u_type;
  logic [31:0] imm_j_type;

  logic [31:0] op_a_imm;
  logic [31:0] op_b_imm;
  logic [31:0] op_c_imm;


  logic [31:0][NumRspTot-1:0] acc_op_a;
  logic [31:0][NumRspTot-1:0] acc_op_b;
  logic [31:0][NumRspTot-1:0] acc_op_c;

  logic [31:0][NumRspTot-1:0] acc_imm_a;
  logic [31:0][NumRspTot-1:0] acc_imm_b;
  logic [31:0][NumRspTot-1:0] acc_imm_c;


  logic [2:0] use_rs;

  logic sources_valid;

  ////////////////////////
  // Instruction Parser //
  ////////////////////////

  // Instruction data
  assign instr_rdata_id   = adapter_req_i.instr;
  assign instr_rdata_id_o = adapter_req_i.instr;

  // Destination register
  assign instr_rd = instr_rdata_id[11:7];

  // Immediate extraction and sign extension
  assign imm_i_type = { {20{instr_rdata_id[31]}}, instr_rdata_id[31:20] };
  assign imm_s_type =
    { {20{instr_rdata_id[31]}}, instr_rdata_id[31:25], instr_rdata_id[11:7] };
  assign imm_b_type =
    { {19{instr_rdata_id[31]}}, instr_rdata_id[31], instr_rdata_id[7],
          instr_rdata_id[30:25], instr_rdata_id[11:8], 1'b0 };
  assign imm_u_type = { instr_rdata_id[31:12], 12'b0 };
  assign imm_j_type =
    { {12{instr_rdata_id[31]}}, instr_rdata_id[19:12], instr_rdata_id[20],
          instr_rdata_id[30:21], 1'b0 };

  // operand muxes
  for (genvar i=0; i<NumRspTot; i++) begin : gen_op_mux
    always_comb begin
      acc_op_a[i] = '0;
      acc_op_b[i] = '0;
      acc_op_c[i] = '0;
      unique case (offl_instr_i[i].imm_a_mux)
        IMM_I:   acc_imm_a[i] = imm_i_type;
        IMM_S:   acc_imm_a[i] = imm_s_type;
        IMM_B:   acc_imm_a[i] = imm_b_type;
        IMM_U:   acc_imm_a[i] = imm_u_type;
        IMM_J:   acc_imm_a[i] = imm_j_type;
        default: acc_imm_a[i] = imm_i_type;
      endcase
      unique case (offl_instr_i[i].imm_b_mux)
        IMM_I:   acc_imm_b[i] = imm_i_type;
        IMM_S:   acc_imm_b[i] = imm_s_type;
        IMM_B:   acc_imm_b[i] = imm_b_type;
        IMM_U:   acc_imm_b[i] = imm_u_type;
        IMM_J:   acc_imm_b[i] = imm_j_type;
        default: acc_imm_b[i] = imm_i_type;
      endcase
      unique case (offl_instr_i[i].imm_c_mux)
        IMM_I:   acc_imm_c[i] = imm_i_type;
        IMM_S:   acc_imm_c[i] = imm_s_type;
        IMM_B:   acc_imm_c[i] = imm_b_type;
        IMM_U:   acc_imm_c[i] = imm_u_type;
        IMM_J:   acc_imm_c[i] = imm_j_type;
        default: acc_imm_c[i] = imm_i_type;
      endcase
      if (offload_accept_i[i]) begin
        acc_op_a[i] = offload_instr_i[i].op_a_mux == OP_RS ? adapter_req_i.rs1_i : acc_imm_a[i];
        acc_op_b[i] = offload_instr_i[i].op_b_mux == OP_RS ? adapter_req_i.rs2_i : acc_imm_b[i];
        acc_op_c[i] = offload_instr_i[i].op_c_mux == OP_RS ? adapter_req_i.rs3_i : acc_imm_c[i];
      end
    end
  end

  /////////////////////
  // Address Encoder //
  /////////////////////

  logic [NumHier-1:0]                   hier_onehot;
  logic [HierAddrWidth-1:0]             hier_addr;
  logic [AccAddrWidth-1:0][NumHier-1:0] acc_addr;
  logic [MaxNumRsp-1:0][NumHier-1:0]    offload_accept_lvl;
  // The first NumRsp[0] requests go to level 0
  // The next NumRsp[1] requests go to level 1
  // ...
  //
  for (genvar i=0; i<NumHier; i++) begin : gen_acc_addr
    localparam SumNumRsp = i == 0 ? 0 : sumn(NumRsp, i-1);
    logic [NumRspTot-1:0] shift_offload_accept;
    assign shift_offload_accept = offload_accept_i >> SumNumRsp;
    assign offload_accept_lvl[i] =
        {{MaxNumRsp-NumRsp[i]{1'b0}}, shift_offload_accept[NumRsp[i]-1:0]};

    // Accelerator address encoder
    onehot_to_bin #(
      .ONEHOT_WIDTH ( MaxNumRsp )
    ) acc_addr_enc_i (
      .onehot ( offload_accept_lvl[i] ),
      .bin    ( acc_addr[i]           )
    );
    // Hierarchy level selsect
    assign hier_onehot[i] = |offload_accept_lvl[NumRsp[i]-1:0];
  end

  // Hierarchy level encoder
  onehot_to_bin #(
    .ONEHOT_WIDTH(NumHier)
  ) hier_addr_enc_i (
    .onehot(hier_onehot),
    .bin(hier_addr)
  );

  /////////////////////////////
  // Assemble Request Struct //
  /////////////////////////////

  // Address
  always_comb begin
    acc_out_fifo_req.addr[AccAddrWidth-1:0] = '0;
    for (int unsigned i=0; i<NumHier; i++) begin
      acc_out_fifo_req.addr[AccAddrWidth-1:0] |= acc_addr;
    end
  end
  assign acc_out_fifo_req.addr[AddrWidth-1:AccAddrWidth] = hier_addr;

  // Operands
  always_comb begin
    acc_out_fifo_req.data_arga = '0;
    acc_out_fifo_req.data_argb = '0;
    acc_out_fifo_req.data_argc = '0;
    use_rs                     = '0;
    adapter_rsp_o.k.writeback  = '0;
    for (int unsigned i=0; i<NumRspTot; i++) begin
      acc_out_fifo_req.data_arga |= offload_accept_i[i] ? acc_op_a[i] : '0;
      acc_out_fifo_req.data_argb |= offload_accept_i[i] ? acc_op_b[i] : '0;
      acc_out_fifo_req.data_argc |= offload_accept_i[i] ? acc_op_c[i] : '0;
      use_rs                     |= offload_accept_i[i] ? offload_instr_i[i].use_rs    : '0;
      adapter_rsp_o.k.writeback  |= offload_accept_i[i] ? offload_instr_i[i].writeback : '0;
    end
  end

  // Instruction Data
  assign acc_out_fifo_req.data_op = instr_rdata_id;
  assign acc_out_fifo_req.id      = instr_rd;

  //////////////////
  // Flow Control //
  //////////////////

  // All source registers are ready if use_rs[i] == rs_valid[i] or ~use_rs[i];
  assign sources_valid = (use_rs ~^ adapter_req_i.q.rs_valid | ~use_rs) == '1;

  assign adapter_rsp_o.k.accept = |offload_accept_i;
  assign acc_out_fifo_valid     = adapter_req_i.q_valid && sources_valid;
  assign adapter_rsp_o.q_ready  = ~adapter_rsp_o.k.accept || (sources_valid && acc_out_fifo_ready);

  // Forward accelerator response
  assign adapter_rsp_o.p       = acc_rsp_i.q;
  assign adapter_rsp_o.p_valid = acc_rsp_i.p_valid;
  assign acc_req_o.p_valid     = adapter_req_i.p_valid;


  /////////////////
  // Output Fifo //
  /////////////////

  // To acc interconnect.
  stream_fifo#(
    .FALL_THROUGH ( 1'b1       ),
    .DEPTH        ( 1          ),
    .T            ( acc_req_chan_t )
  ) acc_req_out_reg (
    .clk_i   ( clk_i             ),
    .rst_ni  ( rst_ni            ),
    .clr_i   ( 1'b0              ),
    .valid_i ( acc_out_fifo_valid     ),
    .ready_o ( acc_out_fifo_ready     ),
    .data_i  ( acc_out_fifo_req       ),
    .valid_o ( acc_req_o.q_valid ),
    .ready_i ( acc_rsp_i.q_ready ),
    .data_o  ( acc_req_o.q       )
  );

  // Sanity Checks
  // pragma translate_off
  `ifndef VERILATOR
  assert property (@(posedge clk_i) $onehot0(offload_accept_i)) else
      $error("Multiple accelerators accepeting request");
  assert property (@(posedge clk_i) (adapter_req_i.q_valid && !adapter_rsp_o.q_ready)
                                    |=> $stable(instr_rdata_id)) else
      $error ("instr_rdata_id is unstable");
  assert property (@(posedge clk_i) (adapter_req_i.q_valid && !adapter_rsp_o.q_ready)
                                    |=> adapter_req_i.q_valid) else
      $error("adapter_req_i.q_valid has been taken away without a ready");
  assert property (@(posedge clk_i)
      (adapter_req_i.q_valid && adapter_rsp_o.q_ready && adapter_rsp_o.q.accept)
          |-> sources_valid) else
      $error("accepted offload request with invalid source registers");
  `endif
  // pragma translate_on

endmodule

module acc_adapter_intf #(
  parameter int unsigned DataWidth         = 32,
  parameter int          NumHier           = 3,
  parameter int          NumRsp[NumHier]   = '{4,2,2},
  // Dependent parameter DO NOT OVERRIDE
  parameter int NumRspTot                  = acc_pkg::sumn(NumRsp, NumHier)
) (
  input clk_i,
  input rst_ni,

  ACC_ADAPTER_BUS    mst,
  ACC_BUS            slv,
  ACC_PREDECODER_BUS prd [NumRspTot]
);
  import acc_pkg::*;

  localparam MaxNumRsp     = maxn(NumRsp, NumHier);
  localparam HierAddrWidth = cf_math_pkg::idx_width(NumHier);
  localparam AccAddrWidth  = cf_math_pkg::idx_width(MaxNumRsp);
  localparam AddrWidth     = HierAddrWidth + AccAddrWidth;

  typedef logic [AddrWidth-1:0] addr_t;
  typedef logic [DataWidth-1:0] data_t;
  typedef logic [4:0]           id_t;

  `ACC_ADAPTER_TYPEDEF_ALL(acc_adapter, data_t, id_t)
  `ACC_TYPEDEF_ALL(acc, addr_t, data_t, id_t)

  offl_instr_t [NumRspTot-1:0] offload_instr;
  logic [NumRspTot-1:0]        offload_accept;
  logic [31:0]                 instr_data;

  // TODO: for consistency, define assignment macro?
  for (genvar i=0; i<NumRspTot; i++) begin : gen_acc_predecoder_intf_assign
    assign offload_accept[i] = prd[i].offload_accept;
    assign offload_instr[i]  = prd[i].offload_instr;
    assign prd[i].instr_data = instr_data;
  end

  acc_adapter_req_t acc_adapter_req;
  acc_adapter_rsp_t acc_adapter_rsp;
  acc_req_t         acc_req;
  acc_rsp_t         acc_rsp;

  acc_adapter #(
    .DataWidth ( DataWidth ),
    .NumHier   ( NumHier   ),
    .NumRsp    ( NumRsp    )
  ) (
    .clk_i            ( clk_i           ),
    .rst_ni           ( rst_ni          ),
    .adapter_req_i    ( acc_adapter_req ),
    .adapter_rsp_o    ( acc_adapter_rsp ),
    .acc_req_o        ( acc_req         ),
    .acc_rsp_i        ( acc_rsp         ),
    .instr_rdata_o    ( instr_data      ),
    .offload_instr_i  ( offload_instr   ),
    .offload_accept_i ( offload_accept  )
  );

endmodule
