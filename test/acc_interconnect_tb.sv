// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

`include "acc_interface/assign.svh"
`include "acc_interface/typedef.svh"

module acc_interconnect_tb  #(
  parameter int unsigned NumReq       = 8,
  parameter int unsigned NumRsp       = 5,
  parameter int unsigned DataWidth    = 32,
  parameter bit          RegisterReq  = 0,
  parameter bit          RegisterRsp  = 0,
  // TB params
  parameter int unsigned NrRandomTransactions = 1000
);

  // dependent parameters
  localparam int unsigned AccAddrWidth  = cf_math_pkg::idx_width(NumRsp);
  localparam int unsigned HierAddrWidth = 1;
  localparam int unsigned AddrWidth     = AccAddrWidth + HierAddrWidth;
  localparam int unsigned ExtIdWidth    = 1+ cf_math_pkg::idx_width(NumReq);
  localparam int unsigned NumHier       = 1;
  localparam int unsigned HierLevel     = 0;


  typedef acc_test::c_req_t # (
    .AddrWidth ( AddrWidth ),
    .DataWidth ( DataWidth ),
    .IdWidth   ( 1         )
  ) tb_mst_c_req_t;

  typedef acc_test::c_rsp_t # (
    .DataWidth ( DataWidth ),
    .IdWidth   ( 1         )
  ) tb_mst_c_rsp_t;

  typedef acc_test::c_req_t # (
    .AddrWidth ( AddrWidth ),
    .DataWidth ( DataWidth ),
    .IdWidth   ( ExtIdWidth  )
  ) tb_slv_c_req_t;

  typedef acc_test::c_rsp_t # (
    .DataWidth    ( DataWidth  ),
    .IdWidth      ( ExtIdWidth )
  ) tb_slv_c_rsp_t;

  // Timing params
  localparam time ClkPeriod = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;

  logic clk, rst_n;

  ACC_C_BUS #(
    .AddrWidth ( AddrWidth ),
    .DataWidth ( DataWidth ),
    .IdWidth   ( 1         )
  ) master [NumReq] ();

  ACC_C_BUS_DV #(
    .AddrWidth ( AddrWidth ),
    .DataWidth ( DataWidth ),
    .IdWidth   ( 1         )
  ) master_dv [NumReq] (clk);

  ACC_C_BUS #(
    .AddrWidth ( AddrWidth ),
    .DataWidth ( DataWidth ),
    .IdWidth   ( 1         )
  ) master_next [NumReq] ();

  ACC_C_BUS #(
    .AddrWidth ( AddrWidth  ),
    .DataWidth ( DataWidth  ),
    .IdWidth   ( ExtIdWidth )
  ) slave [NumRsp] ();

  ACC_C_BUS_DV #(
    .AddrWidth ( AddrWidth  ),
    .DataWidth ( DataWidth  ),
    .IdWidth   ( ExtIdWidth )
  ) slave_dv [NumRsp] (clk);

  for (genvar i=0; i<NumReq; i++) begin : gen_req_if_assignement
    `ACC_C_ASSIGN(master[i], master_dv[i])
  end

  for (genvar i=0; i<NumRsp; i++) begin : gen_resp_if_assignement
    `ACC_C_ASSIGN(slave_dv[i], slave[i])
  end

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

  // -------
  // Monitor
  // -------
  typedef acc_test::acc_c_slv_monitor #(
    // Acc bus interface paramaters;
    .DataWidth ( DataWidth  ),
    .AddrWidth ( AddrWidth  ),
    .IdWidth   ( ExtIdWidth ),
    .NumReq    ( NumReq     ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) acc_c_slv_monitor_t;

  typedef acc_test::acc_c_mst_monitor #(
    // Acc bus interface paramaters;
    .DataWidth ( DataWidth ),
    .AddrWidth ( AddrWidth ),
    .IdWidth   ( 1         ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) acc_c_mst_monitor_t;

  acc_c_mst_monitor_t acc_mst_monitor [NumReq];
  for (genvar i=0; i<NumReq; i++) begin : gen_mst_mon
    initial begin
      acc_mst_monitor[i] = new(master_dv[i]);
      @(posedge rst_n);
      acc_mst_monitor[i].monitor();
    end
  end

  acc_c_slv_monitor_t acc_slv_monitor [NumRsp];
  for (genvar i=0; i<NumRsp; i++) begin : gen_slv_mon
    initial begin
      acc_slv_monitor[i] = new(slave_dv[i]);
      @(posedge rst_n);
      acc_slv_monitor[i].monitor();
    end

  end

  // ------
  // Driver
  // ------
  typedef acc_test::rand_c_slave #(
    // Acc bus interface paramaters;
    .DataWidth ( DataWidth  ),
    .AddrWidth ( AddrWidth  ),
    .IdWidth   ( ExtIdWidth ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) acc_rand_slave_t;

  acc_rand_slave_t rand_c_slave [NumRsp];
  for (genvar i = 0; i < NumRsp; i++) begin : gen_slv_driver
    initial begin
      rand_c_slave[i] = new (slave_dv[i]);
      rand_c_slave[i].reset();
      @(posedge rst_n);
      rand_c_slave[i].run();
    end
  end

  typedef acc_test::rand_c_master #(
    // Acc bus interface paramaters;
    .DataWidth     ( DataWidth     ),
    .AccAddrWidth  ( AccAddrWidth  ),
    .HierAddrWidth ( HierAddrWidth ),
    .IdWidth       ( 1             ),
    .NumRsp        ( '{NumRsp}     ),
    .NumHier       ( NumHier       ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) acc_rand_master_t;

  acc_rand_master_t rand_c_master [NumReq];

  for (genvar i = 0; i < NumReq; i++) begin
    initial begin
      rand_c_master[i] = new (master_dv[i]);
      rand_c_master[i].reset();
      @(posedge rst_n);
      rand_c_master[i].run(NrRandomTransactions);
    end
  end

  // Compare reqs of different parameterizations
  let mstslv_c_reqcompare(req_mst, req_slv) =
    acc_test::compare_c_req#(
      .mst_c_req_t ( tb_mst_c_req_t ),
      .slv_c_req_t ( tb_slv_c_req_t )
    )::do_compare(req_mst, req_slv);

  // Compare rsps of different parameterizations
  let mstslv_c_rspcompare(rsp_mst, rsp_slv) =
    acc_test::compare_c_rsp#(
      .mst_c_rsp_t ( tb_mst_c_rsp_t ),
      .slv_c_rsp_t ( tb_slv_c_rsp_t )
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
  // TODO: Add possibility for no-response requests.
  //       For check if interconnect is correct, this is fine.

  // For each master check that each request sent has been received by
  // the correct slave.
  initial begin
    automatic int nr_requests = 0;
    @(posedge rst_n);
    for (int kk=0; kk<NumReq; kk++) begin // masters k
      automatic int k=kk;
      fork
        for (int ii=0; ii<NumRsp; ii++) begin // slaves i
          fork
            automatic int i=ii;
            forever begin : check_req_path
              automatic tb_mst_c_req_t req_mst;
              automatic tb_slv_c_req_t req_slv;
              automatic tb_slv_c_req_t req_slv_all[NumReq];
              // Master k has sent request to slave i.
              // Check that slave i has received.
              acc_slv_monitor[i].req_mbx[k<<1].get(req_slv);
              acc_mst_monitor[k].req_mbx[i].get(req_mst);
              assert(mstslv_c_reqcompare(req_mst, req_slv)) else begin
                $error("Request Mismatch");
                $display("----------------------------------------");
                $display("Time: %0t, Slave %x received:", $time, i);
                $display("------------------");
                req_slv.display();
                $display("Master %x sent:", k);
                $display("---------------");
                req_mst.display();
                $display("Slave %x mailboxes:", i);
                for (int j=0; j<NumReq; j++) begin
                  $display("Mailbox from Master %x", j);
                  if (acc_slv_monitor[i].req_mbx[j<<1].num() != 0) begin
                    acc_slv_monitor[i].req_mbx[j].peek(req_slv_all[i]);
                    req_slv_all[i].display();
                  end else begin
                    $display("empty");
                  end
                end
              end
              // check that request was intended for slave i
              assert(req_mst.addr == i) else begin
                $error("Request Routing Error");
                $display("req_slv:");
                $display("--------");
                req_slv.display();
                $display("Received at slave %x.", i);
                $display("---------------------");
              end
              // TODO: is this legal? (forked processes modifying same var)
              nr_requests++;
            end // -- forever
          join_none
        end // -- for (int i=0; i<NumRsp; i++)
      join_none
    end
  end

  // For each response received by a master, check that request has been issued.
  initial begin
    automatic int unsigned nr_responses = 0;
    @(posedge rst_n);
    for (int jj=0; jj<NumReq; jj++) begin
      fork
        automatic int j=jj;
        forever begin
          automatic tb_mst_c_rsp_t rsp_mst;
          automatic bit rsp_sender_found = 0;
          acc_mst_monitor[j].rsp_mbx.get(rsp_mst);
          nr_responses++;
          for (int l=0; l<NumRsp; l++) begin
            if (acc_slv_monitor[l].rsp_mbx[j<<1].num() != 0) begin
              automatic tb_slv_c_rsp_t rsp_slv;
              acc_slv_monitor[l].rsp_mbx[j<<1].peek(rsp_slv);
              if (mstslv_c_rspcompare(rsp_mst, rsp_slv)) begin
                acc_slv_monitor[l].rsp_mbx[j<<1].get(rsp_slv);
                rsp_sender_found = 1;
                break;
              end
            end
          end
          assert(rsp_sender_found) else begin
            $error( "Response Routing Error");
            $display("Master %0d received:", j);
            rsp_mst.display();
            for (int l=0; l<NumRsp; l++) begin
              automatic tb_slv_c_rsp_t rsp_slv;
              $display( "Slave %0d -> Master %0d Mailbox", l, j);
              if(acc_slv_monitor[l].rsp_mbx[j<<1].try_peek(rsp_slv)) begin
                rsp_slv.display();
              end else begin
                $display("Empty");
              end
            end


          end
          if (nr_responses == NumReq * NrRandomTransactions) $finish;
        end
      join_none
    end
  end

  final begin
    for (int i=0; i<NumReq; i++) begin
      for (int j=0; j<NumRsp; j++) begin
        assert(acc_mst_monitor[i].req_mbx[j].num() == 0);
        assert(acc_mst_monitor[i].rsp_mbx.num() == 0);
        assert(acc_slv_monitor[j].req_mbx[i].num() == 0);
        assert(acc_slv_monitor[j].rsp_mbx[i].num() == 0);
      end
    end
    $display("Checked for non-empty mailboxes.");
  end

  acc_interconnect_intf #(
    .DataWidth     ( DataWidth     ),
    .HierAddrWidth ( HierAddrWidth ),
    .AccAddrWidth  ( AccAddrWidth  ),
    .HierLevel     ( 0             ),
    .NumReq        ( NumReq        ),
    .NumRsp        ( NumRsp        ),
    .RegisterReq   ( RegisterReq   ),
    .RegisterRsp   ( RegisterRsp   )
  ) dut (
    .clk_i          ( clk         ),
    .rst_ni         ( rst_n       ),
    .acc_c_mst_next ( master_next ),
    .acc_c_mst      ( slave       ),
    .acc_c_slv      ( master      )
  );

  for (genvar i=0; i<NumReq; i++) begin : gen_bypass_tieoff
    assign master_next[i].q_ready = '0;
    assign master_next[i].p_data0 = '0;
    assign master_next[i].p_data1 = '0;
    assign master_next[i].p_dual_writeback = '0;
    assign master_next[i].p_id = '0;
    assign master_next[i].p_rd = '0;
    assign master_next[i].p_error = '0;
    assign master_next[i].p_valid = '0;
  end

endmodule
