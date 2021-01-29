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
  // The number of requesters.
  // parameter int          NumRequesters = -1,
  // The number of responders.
  // parameter int          NumResponders = -1,

  // ISA bit width
  parameter int unsigned DataWidth       = 32,
  // Accelerator Address Width
  parameter int unsigned AccAddrWidth = 5,
  // Id Width (5 + clog2(NumRequesters)
  parameter int unsigned IdWidth         = 5
);

  // localparam int unsigned AccAddrWidth = $clog2(NumResponders) + 1; // +1 for sharing level.
  // localparam int unsigned IdWidthReq      = 5;
  // Extend ID tag on the response path.
  // localparam int unsigned IdxWidth        = cf_math_kg::idx_width(NumRequesters);/
  // localparam int unsigned IdWidthResp     = 5 + IdxWidth;

  typedef logic [DataWidth-1:0] data_t;


  // Request channel (Q).
  logic [AccAddrWidth-1:0] q_addr;
  logic [31:0]                q_data_op;
  data_t                      q_data_arga;
  data_t                      q_data_argb;
  data_t                      q_data_argc;
  logic [IDWidth-1:0]         q_id;
  logic                       q_valid;
  logic                       q_ready;

  // Response Channel (P).
  data_t                  p_data;
  logic [IDWidth-1:0]     p_id;
  logic                   p_error;
  logic                   p_valid;
  logic                   p_ready;

  modport in (
    input  q_addr, q_data_op, q_data_arga, q_data_argb, q_data_argc, q_id, q_valid, p_ready,
    output q_ready, p_data, p_id, p_error, p_valid
  );

  modport out (
    output q_addr, q_data_op, q_data_arga, q_data_argb, q_data_argc, q_id, q_valid, p_ready,
    input  q_ready, p_data, p_id, p_error, p_valid
  );


endinterface

interface ACC_BUS_DV #(
  // The number of requesters
  // parameter int NumRequesters = -1,
  // The number of respondrs
  // parameter int NumResponders = -1,

  // ISA bit width
  parameter int unsigned DataWidth       = 32,
  // Accelerator Address Width
  parameter int unsigned AccAddrWidth = 5,
  // Id Width (5 + clog2(NumRequesters)
  parameter int unsigned IdWidth         = 5
) (
  input logic clk_i
);



  // localparam int unsigned AccAddrWidth = $clog2(NumResponders) + 1; // +1 for sharing level.
  // localparam int unsigned IdWidthReq      = 5;
  // Extend ID tag on the response path.
  // localparam int unsigned IdxWidth       = cf_math_kg::idx_width(NumRequesters);
  // localparam int unsigned IdWidthResp     = 5 + IdxWidth;

  typedef logic [DataWidth-1:0] data_t;


  // Request channel (Q).
  logic [AccAddrWidth-1:0] q_addr;
  logic [31:0]                q_data_op;
  data_t                      q_data_arga;
  data_t                      q_data_argb;
  data_t                      q_data_argc;
  logic [IdWidth-1:0]      q_id;

  logic q_valid;
  logic q_ready;

  // Response Channel (P).
  data_t                  p_data;
  logic [IdWidth-1:0]     p_id;
  logic                   p_error;
  logic                   p_valid;
  logic                   p_ready;

  modport in (
    input  q_addr, q_data_op, q_data_arga, q_data_argb, q_data_argc, q_id, q_valid, p_ready,
    output q_ready, p_data, p_id, p_error, p_valid
  );

  modport out (
    output q_addr, q_data_op, q_data_arga, q_data_argb, q_data_argc, q_id, q_valid, p_ready,
    input  q_ready, p_data, p_id, p_error, p_valid
  );

  modport monitor (
    input  q_addr, q_data_op, q_data_arga, q_data_argb, q_data_argc, q_id, q_valid, p_ready,
    input  q_ready, p_data, p_id, p_error, p_valid
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

  assert property (@(posedge clk_i) (p_valid && !p_ready |=> $stable(p_data)));
  assert property (@(posedge clk_i) (p_valid && !p_ready |=> $stable(p_id)));
  assert property (@(posedge clk_i) (p_valid && !p_ready |=> $stable(p_error)));
  assert property (@(posedge clk_i) (p_valid && !p_ready |=> p_valid));
  `endif
  // pragma translate_on

endinterface
