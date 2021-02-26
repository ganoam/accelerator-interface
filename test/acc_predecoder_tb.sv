// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>



module acc_predecoder_tb #(
);


acc_predecoder_intf #(
  .NumInstr  ( acc_rvb_insn_pkg::rvb32_num_insn ),
  .OfflInstr ( acc_rvb_insn_pkg::rvb32_insn     )
) dut
