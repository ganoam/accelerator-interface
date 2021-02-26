// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

`include "acc_interface/assign.svh"
`include "acc_interface/typedef.svh"

module acc_adapter_tb #(
  parameter int unsigned DataWidth       = 32,
  parameter int          NumHier         = 3,
  parameter int          NumRsp[NumHier] = '{4,2,2},
  parameter int          NumRspTot       = sumn(NumRsp, NumHier),
  // TB Params
  parameter int unsigned NrRandomTransactions = 1000
);

  //TODO: Response Path.

  import acc_pkg::*;
  localparam MaxNumRsp     = maxn(NumRsp, NumHier);
  localparam HierAddrWidth = cf_math_pkg::idx_width(NumHier);
  localparam AccAddrWidth  = cf_math_pkg::idx_width(MaxNumRsp);
  localparam AddrWidth     = HierAddrWidth + AccAddrWidth;

  // Timing params
  localparam time ClkPeriod = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;

  logic clk, rst_n;

  initial begin
    for (int i=0; i<NumHier; i++) begin
     $display("NumRsp[%0d] = %0d", i, NumRsp[i]);
   end
   $display("NumRspTot = %0d", NumRspTot);
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

  typedef acc_test::req_t # (
    .AddrWidth ( AddrWidth ),
    .DataWidth ( DataWidth ),
    .IdWidth   ( 1         )
  ) tb_req_t;

  typedef acc_test::adapter_req_t #(
    .DataWidth ( DataWidth )
  ) tb_adp_req_t;

  typedef acc_test::predecoder_req_t tb_prd_req_t;
  typedef acc_test::predecoder_rsp_t tb_prd_rsp_t;

  /*
  typedef acc_test::adapter_rsp_t #(
    .DataWidth( DataWidth )
  ) tb_adp_rsp_t;
  */

  // From / to core
  ACC_ADAPTER_BUS #(
    .DataWidth ( DataWidth )
  ) master ();

  ACC_ADAPTER_BUS_DV #(
    .DataWidth ( DataWidth )
  ) master_dv ( clk );

  // From / to interconnect
  ACC_BUS #(
    .AddrWidth ( AddrWidth ),
    .DataWidth ( DataWidth ),
    .IdWidth   ( 1         )
  ) slave ();

  ACC_BUS_DV #(
    .AddrWidth ( AddrWidth ),
    .DataWidth ( DataWidth ),
    .IdWidth   ( 1         )
  ) slave_dv ( clk );

  // From / to predecoders
  ACC_PREDECODER_BUS predecoder [NumRspTot] ();

  ACC_PREDECODER_BUS_DV predecoder_dv [NumRspTot] ( clk );

  `ACC_ASSIGN(slave_dv, slave)

  `ACC_ADAPTER_ASSIGN(master, master_dv)

  for (genvar i=0; i<NumRspTot; i++) begin : gen_predecoder_intf_assign
    `ACC_PREDECODER_ASSIGN(predecoder_dv[i], predecoder[i])
  end

  // --------
  // Monitors
  // --------
  typedef acc_test::acc_slv_monitor #(
    // Acc bus interface paramaters;
    .DataWidth ( DataWidth ),
    .AddrWidth ( AddrWidth ),
    .IdWidth   ( 1         ),
    .NumReq    ( 1         ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) acc_slv_monitor_t;

  typedef acc_test::acc_adapter_monitor #(
    .DataWidth ( DataWidth ),
    .TA        ( ApplTime  ),
    .TT        ( TestTime  )
  ) acc_adapter_monitor_t;

  typedef acc_test::acc_predecoder_monitor #(
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) acc_predecoder_monitor_t;


  acc_slv_monitor_t acc_slv_monitor = new(slave_dv);
  initial begin
    @(posedge rst_n);
    acc_slv_monitor.monitor();
  end

  acc_adapter_monitor_t acc_adapter_mst_monitor = new(master_dv);
  initial begin
    @(posedge rst_n);
    acc_adapter_mst_monitor.monitor();
  end

  acc_predecoder_monitor_t acc_predecoder_monitor[NumRspTot];
  for (genvar i=0; i<NumRspTot; i++) begin : gen_predecoder_monitor
    initial begin
      acc_predecoder_monitor[i] = new(predecoder_dv[i]);
      @(posedge rst_n);
      acc_predecoder_monitor[i].monitor();
    end
  end

  // -------
  // Drivers
  // -------

  typedef acc_test::rand_acc_adapter_master#(
    .DataWidth ( DataWidth ),
    .TA        ( ApplTime  ),
    .TT        ( TestTime  )
  ) rand_acc_adapter_master_t;

  typedef acc_test::rand_acc_slave#(
    .AddrWidth ( AddrWidth ),
    .DataWidth ( DataWidth ),
    .IdWidth   ( 1         ),
    .TA        ( ApplTime  ),
    .TT        ( TestTime  )
  ) rand_acc_slave_t;

  typedef acc_test::rand_acc_predecoder_slave_collective #(
    .NumRspTot ( NumRspTot ),
    .TA        ( ApplTime  ),
    .TT        ( TestTime  )
  ) rand_acc_predecoder_slv_coll_t;

  rand_acc_adapter_master_t rand_acc_adapter_master = new(master_dv);
  initial begin
    rand_acc_adapter_master.reset();
    @(posedge rst_n);
    rand_acc_adapter_master.run(NrRandomTransactions);
  end

  rand_acc_predecoder_slv_coll_t rand_acc_predecoder_slv_coll = new(predecoder_dv);
  initial begin
    rand_acc_predecoder_slv_coll.reset();
    @(posedge rst_n);
    rand_acc_predecoder_slv_coll.run();
  end

  rand_acc_slave_t rand_acc_slave = new(slave_dv);
  initial begin
    rand_acc_slave.reset();
    @(posedge rst_n);
    // For now, do not generate responses.
    // TODO: Check writeback through adapter.
    rand_acc_slave.recv_requests();
  end

  // Request generation checker
  let check_req(adp_req, prd_rsp, acc_req) =
    acc_test::adp_check_req #(
      .acc_req_t ( tb_req_t     ),
      .adp_req_t ( tb_adp_req_t ),
      .prd_rsp_t ( tb_prd_rsp_t )
    )::do_check(adp_req, prd_rsp, acc_req);

  // Scoreboard
  // For each request entering the interconnect (acc_slave_monitor), check
  //  - Address corresponds to accepting predecoder
  //  - Operands generated from adapter_master using mux signals from
  //  predecoder
  //  - instr_data properly forwarded
  initial begin
    automatic int nr_requests = 0;
    @(posedge rst_n);
    fork
      // Check accepted requests
      forever begin
        automatic tb_adp_req_t adp_req;
        automatic tb_req_t     acc_req;
        automatic tb_prd_rsp_t prd_rsp;
        automatic tb_prd_req_t prd_req;
        automatic int prd_id, i;
        // Wait for a request at the interconnect output
        acc_slv_monitor.req_mbx[0].get(acc_req);

        // get predecoder ID
        prd_id = acc_req.addr[AccAddrWidth-1:0];
        i = 0;
        while ( i != acc_req.addr[AddrWidth-1:AccAddrWidth]) begin
          prd_id += NumRsp[i];
          i++;
        end
        // get accepting predecoder response and request structures and
        // corresponding adapter request.
        assert(acc_predecoder_monitor[prd_id].rsp_mbx.try_get(prd_rsp));
        assert(acc_predecoder_monitor[prd_id].req_mbx.try_get(prd_req));
        assert(acc_adapter_mst_monitor.req_mbx.try_get(adp_req));
        // Check we are talking about the same request.
        assert((prd_req.instr_data ^ (adp_req.instr_data ^ acc_req.instr_data)) == '0);
        // Check accelerator request integrity
        assert(check_req(adp_req, prd_rsp, acc_req)) else begin
          $error("Request Assembly Error.");
          $display("===");
          $display("Adapter Request:");
          $display("---");
          adp_req.display();
          $display("---");
          $display("Predecoder Response:");
          $display("---");
          prd_rsp.display();
          $display("---");
          $display("Accelerator Request");
          $display("---");
          acc_req.display();
        end
        nr_requests++;
        $display("Time %t. Request Accepted. Total Requests: %0d", $time,nr_requests);
      end

      // check rejected requests
      forever begin
        automatic tb_adp_req_t adp_req;
        // Wait for rejected request
        acc_adapter_mst_monitor.req_mbx_rejected.get(adp_req);
        // Check if any predecoder wanted to accept this request.
        for (int i = 0; i< NumRspTot; i++) begin
          automatic tb_prd_req_t prd_req;
          if (acc_predecoder_monitor[i].req_mbx.try_peek(prd_req)) begin
            // Instruction data is `randc`
            // no repetitions in 2**32 samples
            assert (prd_req.instr_data != adp_req.instr_data) else
              $error("Mistakenly rejected adapter request");
          end
        end
        nr_requests++;
        $display("Time: %t. Request Rejected. Total Requests: %0d", $time, nr_requests);
      end
      forever begin
        // wait for end of sim.
        if (nr_requests == NrRandomTransactions) begin
          repeat(1000) @(posedge clk);
          $finish;
        end
        @(posedge clk);
      end
    join_none
  end

  final begin
    for (int i=0; i<NumRspTot; i++) begin
      assert(acc_predecoder_monitor[i].req_mbx.num() == 0);
    end
    assert(acc_adapter_mst_monitor.req_mbx.num() == 0);
    assert(acc_adapter_mst_monitor.req_mbx_rejected.num() == 0);
    assert(acc_slv_monitor.req_mbx[0].num() == 0);
    $display("Checked for non-empty mailboxes (request path)");
  end

  // DUT instantiation
  acc_adapter_intf #(
    .DataWidth ( DataWidth ),
    .NumHier   ( NumHier   ),
    .NumRsp    ( NumRsp    )
  ) dut (
    .clk_i  ( clk        ),
    .rst_ni ( rst_n      ),
    .mst    ( master     ),
    .slv    ( slave      ),
    .prd    ( predecoder )
  );




endmodule
