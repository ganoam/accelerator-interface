// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

// Accelerator Interface
//
// This interface provides two channels, one for requests and one for
// responses. Both channels have a valid/ready handshake. The sender sets the
// channel signals and pulls valid high. Once pulled high, valid must remain
// high and none of the signals may change. The transaction completes when both
// valid and ready are high. Valid must not depend on ready.
// The requester can offload any RISC-V instruction together with its operands
// and destination register address.
// Not all offloaded instructions necessarily result in a response. The
// offloading entity must be aware if a write-back is to be expected.
// For further details see docs/index.md.

interface ACC_BUS #(
  // ISA bit width
  parameter int unsigned DataWidth    = 32,
  // Address Width
  parameter int          AddrWidth    = -1,
  // ID Width
  parameter int          IdWidth      = -1
);

  typedef logic [DataWidth-1:0] data_t;
  typedef logic [AddrWidth-1:0] addr_t;
  typedef logic [IdWidth-1:0]   id_t;

  // Request channel (Q).
  addr_t       q_addr;
  logic [31:0] q_data_op;
  data_t       q_data_arga;
  data_t       q_data_argb;
  data_t       q_data_argc;
  id_t         q_id;
  logic        q_valid;
  logic        q_ready;

  // Response Channel (P).
  data_t p_data0;
  data_t p_data1;
  logic  p_dual_writeback;
  id_t   p_id;
  logic  p_error;
  logic  p_valid;
  logic  p_ready;

  modport in (
    input  q_addr, q_data_op, q_data_arga, q_data_argb, q_data_argc, q_id, q_valid, p_ready,
    output q_ready, p_data0, p_data1, p_dual_writeback, p_id, p_error, p_valid
  );

  modport out (
    output q_addr, q_data_op, q_data_arga, q_data_argb, q_data_argc, q_id, q_valid, p_ready,
    input  q_ready, p_data0, p_data1, p_dual_writeback, p_id, p_error, p_valid
  );


endinterface

interface ACC_BUS_DV #(
  // ISA bit width
  parameter int unsigned DataWidth       = 32,
  // Address Width
  parameter int          AddrWidth       = -1,
  // ID Width
  parameter int          IdWidth         = -1
) (
  input logic clk_i
);

  typedef logic [DataWidth-1:0]    data_t;
  typedef logic [AddrWidth-1:0]    addr_t;
  typedef logic [IdWidth-1:0]      id_t;

  // Request channel (Q).
  addr_t       q_addr;
  logic [31:0] q_data_op;
  data_t       q_data_arga;
  data_t       q_data_argb;
  data_t       q_data_argc;
  id_t         q_id;
  logic        q_valid;
  logic        q_ready;

  // Response Channel (P).
  data_t p_data0;
  data_t p_data1;
  logic  p_dual_writeback;
  id_t   p_id;
  logic  p_error;
  logic  p_valid;
  logic  p_ready;

  modport in (
    input  q_addr, q_data_op, q_data_arga, q_data_argb, q_data_argc, q_id, q_valid, p_ready,
    output q_ready, p_data0, p_data1, p_dual_writeback, p_id, p_error, p_valid
  );

  modport out (
    output q_addr, q_data_op, q_data_arga, q_data_argb, q_data_argc, q_id, q_valid, p_ready,
    input  q_ready, p_data0, p_data1, p_dual_writeback, p_id, p_error, p_valid
  );

  modport monitor (
    input  q_addr, q_data_op, q_data_arga, q_data_argb, q_data_argc, q_id, q_valid, p_ready,
    input  q_ready, p_data0, p_data1, p_dual_writeback, p_id, p_error, p_valid
  );

  // pragma translate_off
  `ifndef VERILATOR
  assert property (@(posedge clk_i) (q_valid && !q_ready |=> $stable(q_addr)));
  assert property (@(posedge clk_i) (q_valid && !q_ready |=> $stable(q_data_op)));
  assert property (@(posedge clk_i) (q_valid && !q_ready |=> $stable(q_data_arga)));
  assert property (@(posedge clk_i) (q_valid && !q_ready |=> $stable(q_data_argb)));
  assert property (@(posedge clk_i) (q_valid && !q_ready |=> $stable(q_data_argc)));
  assert property (@(posedge clk_i) (q_valid && !q_ready |=> $stable(q_id)));
  assert property (@(posedge clk_i) (q_valid && !q_ready |=> q_valid));

  assert property (@(posedge clk_i) (p_valid && !p_ready |=> $stable(p_data0)));
  assert property (@(posedge clk_i) (p_valid && !p_ready |=> $stable(p_data1)));
  assert property (@(posedge clk_i) (p_valid && !p_ready |=> $stable(p_dual_writeback)));
  assert property (@(posedge clk_i) (p_valid && !p_ready |=> $stable(p_id)));
  assert property (@(posedge clk_i) (p_valid && !p_ready |=> $stable(p_error)));
  assert property (@(posedge clk_i) (p_valid && !p_ready |=> p_valid));
  `endif
  // pragma translate_on

endinterface

interface ACC_ADAPTER_BUS #(
  // ISA bit Width
  parameter int DataWidth = 32,
  parameter int AddrWidth = -1
);

  typedef logic [DataWidth-1:0] data_t;
  typedef logic [AddrWidth-1:0] addr_t;
  typedef logic [4:0]           id_t;

  // Request Channel (Q)
  logic [31:0] q_instr;
  data_t       q_rs1;
  data_t       q_rs2;
  data_t       q_rs3;
  logic [2:0]  q_rs_valid;
  logic        q_valid;

  // Acknowledge Channel (K)
  logic       k_accept;
  logic [1:0] k_writeback;
  logic       q_ready;

  // Response Channel (P)
  data_t                  p_data;
  id_t                    p_id;
  logic                   p_error;
  logic                   p_valid;
  logic                   p_ready;

  modport in (
    input q_instr, q_rs1, q_rs2, q_rs3, q_rs_valid, q_valid, p_ready,
    output k_accept, k_writeback, q_ready,
    output p_data, p_id, p_error, p_valid
  );

  modport out (
    output q_instr, q_rs1, q_rs2, q_rs3, q_rs_valid, q_valid, p_ready,
    input k_accept, k_writeback, q_ready,
    input p_data, p_id, p_error, p_valid
  );


endinterface

interface ACC_ADAPTER_BUS_DV #(
  // ISA bit Width
  parameter int DataWidth = 32,
  parameter int AddrWidth = -1

) (
  input clk_i
);

  typedef logic [DataWidth-1:0] data_t;
  typedef logic [AddrWidth-1:0] addr_t;
  typedef logic [4:0]           id_t;

  // Request Channel (Q)
  logic [31:0] q_instr;
  data_t       q_rs1;
  data_t       q_rs2;
  data_t       q_rs3;
  logic [2:0]  q_rs_valid;
  logic        q_valid;

  // Acknowledge Channel (K)
  logic       k_accept;
  logic [1:0] k_writeback;
  logic       q_ready;

  // Response Channel (P)
  data_t                  p_data;
  id_t                    p_id;
  logic                   p_error;
  logic                   p_valid;
  logic                   p_ready;

  modport in (
    input q_instr, q_rs1, q_rs2, q_rs3, q_rs_valid, q_valid, p_ready,
    output k_accept, k_writeback, q_ready,
    output p_data, p_id, p_error, p_valid
  );

  modport out (
    output q_instr, q_rs1, q_rs2, q_rs3, q_rs_valid, q_valid, p_ready,
    input k_accept, k_writeback, q_ready,
    input p_data, p_id, p_error, p_valid
  );

  modport monitor (
    output q_instr, q_rs1, q_rs2, q_rs3, q_rs_valid, q_valid, p_ready,
    input k_accept, k_writeback, q_ready,
    input p_data, p_id, p_error, p_valid
  );

  // pragma translate_off
  `ifndef VERILATOR

  // q channel
  assert property (@(posedge clk_i) (q_valid && !q_ready |=> q_valid));
  assert property (@(posedge clk_i) (q_valid && !q_ready |=> $stable(q_instr)));

  assert property (@(posedge clk_i) (q_valid && q_rs_valid[0] && !q_ready |=> q_rs_valid[0]));
  assert property (@(posedge clk_i) (q_valid && q_rs_valid[1] && !q_ready |=> q_rs_valid[1]));
  assert property (@(posedge clk_i) (q_valid && q_rs_valid[2] && !q_ready |=> q_rs_valid[2]));
  assert property (@(posedge clk_i) (q_valid && q_rs_valid[0] && !q_ready |=> $stable(q_rs1)));
  assert property (@(posedge clk_i) (q_valid && q_rs_valid[1] && !q_ready |=> $stable(q_rs2)));
  assert property (@(posedge clk_i) (q_valid && q_rs_valid[2] && !q_ready |=> $stable(q_rs3)));

  // p channel
  assert property (@(posedge clk_i) (p_valid && !p_ready |=> $stable(p_data)));
  assert property (@(posedge clk_i) (p_valid && !p_ready |=> $stable(p_id)));
  assert property (@(posedge clk_i) (p_valid && !p_ready |=> $stable(p_error)));
  assert property (@(posedge clk_i) (p_valid && !p_ready |=> p_valid));

  `endif
  // pragma translate_on
endinterface

interface ACC_PREDECODER_BUS;

  acc_pkg::offl_instr_t offload_instr;
  logic                 offload_accept;
  logic [31:0]          instr_data;

  modport in (
    input instr_data,
    output offload_accept, offload_instr
  );

  modport out (
    input instr_data,
    output offload_accept, offload_instr
  );

endinterface

interface ACC_PREDECODER_BUS_DV (
  input clk_i
);

  acc_pkg::offl_instr_t offload_instr;
  logic                 offload_accept;
  logic [31:0]          instr_data;

  modport in (
    input instr_data,
    output offload_accept, offload_instr
  );

  modport out (
    input instr_data,
    output offload_accept, offload_instr
  );

  modport monitor (
    input instr_data,
    input offload_accept, offload_instr
  );
endinterface
