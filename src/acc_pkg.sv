// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

package acc_pkg;
  parameter int unsigned NumReq        = 1;
  parameter int unsigned NumRespPriv   = 1;
  parameter int unsigned NumRespShared = 1;

  // maximum number of responders per level
  parameter MaxNumResp   = NumRespShared > NumRespPriv ? NumRespShared : NumRespPriv;
  parameter AccAddrWidth = clog2(MaxNumResp) + 1;

  localparam int unsigned IdxWidth = cf_math_kg::idx_width(NumRequesters);/
  localparam int unsigned IdWidth  = 5 + IdxWidth;


endpackage
