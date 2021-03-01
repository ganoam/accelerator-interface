
// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

`include "acc_interface/assign.svh"
`include "acc_interface/typedef.svh"

module acc_cluster_interconnect_tb  #(
  parameter int DataWidth            = 32,
  parameter int NumHier              = 3,
  parameter int NumReq[NumHier]      = '{1,2,4},
  parameter int NumRsp[NumHier]      = '{4,2,2},
  parameter int RegisterReq[NumHier] = '{0,0,0},
  parameter int RegisterRsp[NumHier] = '{0,0,0},
  // TB params
  parameter int unsigned NrRandomTransactions = 1000
);

  import acc_pkg::*;

  // dependent parameters
  localparam int unsigned MaxNumRsp = maxn(NumRsp, NumHier);
  localparam int unsigned AccAddrWidth = cf_math_pkg::idx_width(MaxNumRsp);
  localparam int unsigned HierAddrWidth = cf_math_pkg::idx_width(NumHier);
  localparam int unsigned AddrWidth = AccAddrWidth + HierAddrWidth;

  localparam int unsigned TotNumReq = maxn(NumReq, NumHier);

  // Timing params
  localparam time ClkPeriod = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;

  // Global counters.
  int unsigned nr_responses = 0;
  int unsigned nr_requests = 0;

  logic clk, rst_n;

  // ----------------
  // Clock generation
  // ----------------
  initial begin
    rst_n = 0;
    repeat (3) begin
      #(ClkPeriod/2) clk = 0;
      #(ClkPeriod/2) clk = 1;
    end
    rst_n = 1;
    forever begin
      #(ClkPeriod/2) clk = 0;
      #(ClkPeriod/2) clk = 1;
    end
  end

  typedef acc_test::req_t # (
    .AddrWidth ( AddrWidth ),
    .DataWidth ( DataWidth ),
    .IdWidth   ( 1         )
  ) tb_mst_req_t;

  typedef acc_test::rsp_t # (
    .DataWidth ( DataWidth ),
    .IdWidth   ( 1         )
  ) tb_mst_rsp_t;


  // ------
  // Master
  // ------
  //
  // Driver
  typedef acc_test::rand_acc_master #(
    // Acc bus interface paramaters;
    .DataWidth     ( DataWidth     ),
    .AccAddrWidth  ( AccAddrWidth  ),
    .HierAddrWidth ( HierAddrWidth ),
    .IdWidth       ( 1             ),
    .NumRsp        ( NumRsp        ),
    .NumHier       ( NumHier       ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) acc_rand_master_t;

  // Monitor
  typedef acc_test::acc_mst_monitor #(
    // Acc bus interface paramaters;
    .DataWidth ( DataWidth ),
    .AddrWidth ( AddrWidth ),
    .IdWidth   ( 1         ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) acc_mst_monitor_t;

    ACC_BUS #(
      .AddrWidth ( AddrWidth ),
      .DataWidth ( DataWidth ),
      .IdWidth   ( 1         )
    ) master [(NumHier+1) * TotNumReq] ();

    ACC_BUS_DV #(
      .AddrWidth ( AddrWidth ),
      .DataWidth ( DataWidth ),
      .IdWidth   ( 1         )
    ) master_dv [TotNumReq] (clk);


    for (genvar i=0; i<TotNumReq; i++) begin : gen_req_if_assignement
      `ACC_ASSIGN(master[i], master_dv[i])
    end

    acc_mst_monitor_t acc_mst_monitor [TotNumReq];
    for (genvar i=0; i<TotNumReq; i++) begin : gen_mst_mon
      initial begin
        acc_mst_monitor[i] = new(master_dv[i]);
        @(posedge rst_n);
        acc_mst_monitor[i].monitor();
      end
    end

    acc_rand_master_t rand_acc_master [TotNumReq];

    for (genvar i=0; i<TotNumReq; i++) begin
      initial begin
        rand_acc_master[i] = new (master_dv[i]);
        rand_acc_master[i].reset();
        @(posedge rst_n);
        rand_acc_master[i].run(NrRandomTransactions);
      end
    end

  for (genvar j=0; j<NumHier; j++) begin : gen_interconnect_lvl
    localparam int unsigned IdxWidth = cf_math_pkg::idx_width(NumReq[j]);
    localparam int unsigned ExtIdWidth = 1 + IdxWidth;
    localparam int unsigned NumCopies = TotNumReq / NumReq[j];
    for (genvar k=0; k<NumCopies; k++) begin : gen_lvl_cpy
      // -----
      // Slave
      // -----
      typedef acc_test::req_t # (
        .AddrWidth ( AddrWidth  ),
        .DataWidth ( DataWidth  ),
        .IdWidth   ( ExtIdWidth )
      ) lvl_slv_req_t;

      typedef acc_test::rsp_t # (
        .DataWidth    ( DataWidth  ),
        .IdWidth      ( ExtIdWidth )
      ) lvl_slv_rsp_t;

      // Monitor
      typedef acc_test::acc_slv_monitor #(
        // Acc bus interface paramaters;
        .DataWidth ( DataWidth  ),
        .AddrWidth ( AddrWidth  ),
        .IdWidth   ( ExtIdWidth ),
        .NumReq    ( NumReq[j]  ),
        // Stimuli application and test time
        .TA ( ApplTime ),
        .TT ( TestTime )
      ) acc_slv_monitor_t;

      // Driver
      typedef acc_test::rand_acc_slave #(
        // Acc bus interface paramaters;
        .DataWidth ( DataWidth  ),
        .AddrWidth ( AddrWidth  ),
        .IdWidth   ( ExtIdWidth ),
        // Stimuli application and test time
        .TA ( ApplTime ),
        .TT ( TestTime )
      ) acc_rand_slave_t;

      ACC_BUS #(
        .AddrWidth ( AddrWidth  ),
        .DataWidth ( DataWidth  ),
        .IdWidth   ( ExtIdWidth )
      ) slave [NumRsp[j]] ();

      ACC_BUS_DV #(
        .AddrWidth ( AddrWidth  ),
        .DataWidth ( DataWidth  ),
        .IdWidth   ( ExtIdWidth )
      ) slave_dv [NumRsp[j]] (clk);


      for (genvar i=0; i<NumRsp[j]; i++) begin : gen_resp_if_assignement
        `ACC_ASSIGN(slave_dv[i], slave[i])
      end

      acc_slv_monitor_t acc_slv_monitor [NumRsp[j]];
      for (genvar i=0; i<NumRsp[j]; i++) begin : gen_slv_mon
        initial begin
          acc_slv_monitor[i] = new(slave_dv[i]);
          @(posedge rst_n);
          acc_slv_monitor[i].monitor();
        end
      end

      acc_rand_slave_t rand_acc_slave [NumRsp[j]];
      for (genvar i=0; i<NumRsp[j]; i++) begin : gen_slv_driver
        initial begin
          rand_acc_slave[i] = new (slave_dv[i]);
          rand_acc_slave[i].reset();
          @(posedge rst_n);
          rand_acc_slave[i].run();
        end
      end

      // Compare reqs of different parameterizations
      let mstslv_reqcompare(req_mst, req_slv) =
        acc_test::compare_req#(
          .mst_req_t ( tb_mst_req_t ),
          .slv_req_t ( lvl_slv_req_t )
        )::do_compare(req_mst, req_slv);

      // Compare rsps of different parameterizations
      let mstslv_rspcompare(rsp_mst, rsp_slv) =
        acc_test::compare_rsp#(
          .mst_rsp_t ( tb_mst_rsp_t ),
          .slv_rsp_t ( lvl_slv_rsp_t )
        )::do_compare(rsp_mst, rsp_slv);

      // ----------
      // Scoreboard
      // ----------
      // For each master check that each request sent has been received by
      // the correct slave.
      // For each slave, check that each response sent has been received by
      // the correct master.
      // Stop when all responses have been received.
      //
      // TODO: This add possibility for no-response requests.
      //       For check if interconnect is correct, this is fine.

      // For each master check that each request sent has been received by
      // the correct slave.
      initial begin
        // automatic int nr_requests=0;
        @(posedge rst_n);
        for (int mm=0; mm<NumReq[j]; mm++) begin // masters m
          // find the appropriate master indices:
          automatic int M=mm + k*NumReq[j]; // global index
          automatic int m=mm;               // seen from interconnect j,k
          fork
            for (int ss=0; ss<NumRsp[j]; ss++) begin // slaves s
              fork
                automatic int s=ss;
                automatic int S=ss + TotNumReq*j; // XXX
                forever begin : check_req_path
                  automatic tb_mst_req_t req_mst;
                  automatic lvl_slv_req_t req_slv;
                  automatic lvl_slv_req_t req_slv_all[NumReq[j]];
                  // Master m has sent request to slave s.
                  // Check that slave i has received.
                  acc_slv_monitor[s].req_mbx[m<<1].get(req_slv);
                  acc_mst_monitor[M].req_mbx[S].get(req_mst);
                  assert(mstslv_reqcompare(req_mst, req_slv)) else begin
                    $error("Request Mismatch");
                    $display("----------------------------------------");
                    $display("Time: %0t, Slave %x (level %x, copy %x) received:", $time, s, j,k);
                    $display("------------------");
                    req_slv.display();
                    $display("Master %x sent:", M);
                    $display("---------------");
                    req_mst.display();
                    $display("Slave %x (level %x, copy %x) mailboxes:", s, j,k);
                    for (int l=0; l<NumReq[j]; l++) begin

                      automatic int L=l+k*NumReq[j];
                      $display("Mailbox from Master %x", L);
                      if (acc_slv_monitor[s].req_mbx[l<<1].num() != 0) begin
                        acc_slv_monitor[s].req_mbx[l<<1].peek(req_slv_all[s]);
                        req_slv_all[s].display();
                      end else begin
                        $display("empty");
                      end
                    end
                  end
                  // check that request was intended for slave i
                  assert(req_mst.addr == S) else begin
                    $error("Request Routing Error");
                    $display("req_slv:");
                    $display("--------");
                    req_slv.display();
                    $display("Received at slave %x.", s);
                    $display("---------------------");
                  end
                  nr_requests++;
                end
              join_none
            end
          join_none
        end
      end

      // For each response received by a master, check that request has been issued.
      initial begin
        @(posedge rst_n);
        for (int mm=0; mm<NumReq[j]; mm++) begin
          fork
            automatic int M=mm + k*NumReq[j]; // global index
            automatic int m=mm;               // seen from interconnect j,k
            forever begin
              automatic tb_mst_rsp_t rsp_mst;
              automatic bit rsp_sender_found;
              if (acc_mst_monitor[M].rsp_mbx.num() != 0) begin
                // acc_mst_monitor[M].rsp_mbx.peek(rsp_mst);
                // rsp_mst.display();
                for (int s=0; s<NumRsp[j]; s++) begin
                  if (acc_slv_monitor[s].rsp_mbx[m<<1].num() != 0) begin
                    automatic tb_mst_rsp_t rsp_mst;
                    automatic lvl_slv_rsp_t rsp_slv;
                    acc_mst_monitor[M].rsp_mbx.peek(rsp_mst);
                    acc_slv_monitor[s].rsp_mbx[m<<1].peek(rsp_slv);
                    // $display("slv rsp:");
                    // rsp_slv.display();
                    // $display("mst rsp:");
                    // rsp_mst.display();
                    if (mstslv_rspcompare(rsp_mst, rsp_slv)) begin
                      acc_slv_monitor[s].rsp_mbx[m<<1].get(rsp_slv);
                      acc_mst_monitor[M].rsp_mbx.get(rsp_mst);
                      rsp_sender_found |= 1;
                      // rsp_mst.display();
                      // rsp_slv.display();
                      break;
                    end
                  end
                end
                // Could have been sent by responder on another level... Remove assert.
                // assert(rsp_sender_found) else $error( "Response Routing Error");
                if (rsp_sender_found) begin
                   nr_responses++;
                end else begin
                  @(posedge clk);
                end
              end else begin
                @(posedge clk);
              end
              if (nr_responses == TotNumReq * NrRandomTransactions) $finish;
            end
          join_none
        end
      end

      final begin
        for (int m=0; m<NumReq[j]<<1; m++) begin
          for (int s=0; s<NumRsp[j]; s++) begin
            assert(acc_slv_monitor[s].req_mbx[m].num() == 0);
            assert(acc_slv_monitor[s].rsp_mbx[m].num() == 0);
          end
        end
        $display("Checked for non-empty slave mailboxes on hierarchy level %0d, copy %0d", j,k);
      end

      // --------------------------
      // Interconnect Instantiation
      // --------------------------
      // on each level j:
      // Total number of masters: TotNumReq.
      // Number of masters sharing each interconnect level: NumReq[j]
      // Number of copies of interconnect + slave devices: K = TotNumReq / NumReq[j]
      // The following identity holds: K*NumReq[j] == TotNumReq

      // Input range to interconnect
      localparam int unsigned in_mst_start = j*TotNumReq +     k*NumReq[j];
      localparam int unsigned in_mst_stop  = j*TotNumReq + (k+1)*NumReq[j]-1;

      // Connection to next-level interconnect (1:1 signal forwarding)
      localparam int unsigned out_mst_start = (j+1)*TotNumReq +     k*NumReq[j];
      localparam int unsigned out_mst_stop  = (j+1)*TotNumReq + (k+1)*NumReq[j]-1;

      acc_interconnect_intf #(
        .DataWidth     ( DataWidth      ),
        .HierAddrWidth ( HierAddrWidth  ),
        .AccAddrWidth  ( AccAddrWidth   ),
        .HierLevel     ( j              ),
        .NumReq        ( NumReq[j]      ),
        .NumRsp        ( NumRsp[j]      ),
        .RegisterReq   ( RegisterReq[j] ),
        .RegisterRsp   ( RegisterRsp[j] )
      ) dut (
        .clk_i           ( clk                                ),
        .rst_ni          ( rst_n                              ),
         .acc_c_mst_next ( master[out_mst_start:out_mst_stop] ),
         .acc_c_slv      ( master[in_mst_start:in_mst_stop]   ),
        .acc_c_mst       ( slave                              )
      );
      if (j==NumHier-1) begin : gen_byass_tieoff
        for (genvar l=out_mst_start; l<=out_mst_stop; l++) begin: gen_mst_tieoff
          assign master[l].q_ready = '0;
          assign master[l].p_data0 = '0;
          assign master[l].p_data1 = '0;
          assign master[l].p_dual_writeback = '0;
          assign master[l].p_id = '0;
          assign master[l].p_rd = '0;
          assign master[l].p_error = '0;
          assign master[l].p_valid = '0;
        end
      end
    end
  end

  final begin
    for (int m=0; m<TotNumReq; m++) begin
      for (int l=0; l<NumHier; l++) begin
        for (int s=0; s<NumRsp[l]; s++) begin
          assert(acc_mst_monitor[m].req_mbx[s].num() == 0);
          assert(acc_mst_monitor[m].rsp_mbx.num() == 0);
        end
      end
    end
    $display("Checked for non-empty master mailboxes.");
  end
endmodule
