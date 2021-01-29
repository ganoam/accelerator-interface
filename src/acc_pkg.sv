// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

`include "acc_interface/typedef.svh"


package acc_pkg;
  parameter int unsigned NumReq            = 1;
  parameter int unsigned NumRspPriv        = 1;
  parameter int unsigned NumRspShared      = 1;
  parameter int unsigned DataWidth         = 32;
  parameter bit          RegisterReqPriv   = 1'b0;
  parameter bit          RegisterReqShared = 1'b0;
  parameter bit          RegisterRspPriv   = 1'b0;
  parameter bit          RegisterRspShared = 1'b0;

  // maximum number of responders per level
  parameter MaxNumRsp   = NumRspShared > NumRspPriv ? NumRspShared : NumRspPriv;
  parameter AccAddrWidth = $clog2(MaxNumRsp) + 1;

  localparam int unsigned IdxWidth = cf_math_pkg::idx_width(NumReq);
  localparam int unsigned IdWidth  = 5 + IdxWidth;

  typedef logic [DataWidth-1:0] data_t;
  typedef logic [IdWidth-1:0]   id_t;
  typedef logic [AccAddrWidth-1:0] addr_t;

  // typedef acc_req_t,
  // typedef acc_req_chan_t,
  // typedef acc_rsp_t,
  // typedef acc_rsp_chan_t,
  `ACC_TYPEDEF_ALL(acc, addr_t, data_t, id_t)

endpackage
