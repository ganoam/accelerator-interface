#!/bin/bash
# Copyright 2020 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51
#
# Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
# Andreas Kurth  <akurth@iis.ee.ethz.ch>


set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

[ ! -z "$VSIM" ] || VSIM=vsim

call_vsim_gui() {
  echo "log -r /*;  do util/waves.do; view -new wave; do util/waves_xbars.do; run -all;" | $VSIM -gui -coverage -voptargs='+acc +cover=sbecft' "$@" | tee vsim.log 2>&1
    grep "Errors: 0," vsim.log
}

all_vsim_gui acc_interconnect_tb
