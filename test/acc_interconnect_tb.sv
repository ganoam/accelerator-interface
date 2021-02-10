// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

`include "acc_interface/assign.svh"
`include "acc_interface/typedef.svh"

module acc_interconnect_tb  #(
  // Interconnect parameters from pkg
  parameter int unsigned NumReq       = 8,
  parameter int unsigned NumRsp       = 5,
  parameter int unsigned DataWidth    = 32,
  parameter bit          RegisterReq  = 0,
  parameter bit          RegisterRsp  = 0,
  // TB params
  parameter int unsigned NrRandomTransactions = 1000
);

  // dependent parameters
  localparam int unsigned AccAddrWidth = $clog2(NumRsp);
  localparam int unsigned IdWidth = cf_math_pkg::idx_width(NumReq);

  typedef logic [DataWidth-1:0]    data_t;
  typedef logic [IdWidth-1:0]      id_t;
  typedef logic [AccAddrWidth-1:0] addr_t;

  `ACC_TYPEDEF_ALL(acc, addr_t, data_t, id_t)

  typedef acc_test::req_t # (
    .AccAddrWidth ( AccAddrWidth ),
    .DataWidth    ( DataWidth    ),
    .IdWidth      ( IdWidth      ),
    .NumRsp       ( NumRsp       )
  ) tb_req_t;


  typedef acc_test::rsp_t # (
    .DataWidth    ( DataWidth ),
    .IdWidth      ( IdWidth   )
  ) tb_rsp_t;

  // Timing params
  localparam time ClkPeriod = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;

  logic clk, rst_n;

  ACC_BUS #(
    .AccAddrWidth(AccAddrWidth),
    .DataWidth(DataWidth),
    .IdWidth(IdWidth)
  ) master [NumReq] ();

  ACC_BUS_DV #(
    .AccAddrWidth(AccAddrWidth),
    .DataWidth(DataWidth),
    .IdWidth(IdWidth)
  ) master_dv [NumReq] (clk);


  ACC_BUS #(
    .AccAddrWidth(AccAddrWidth),
    .DataWidth(DataWidth),
    .IdWidth(IdWidth)
  ) slave [NumRsp] ();

  ACC_BUS_DV #(
    .AccAddrWidth(AccAddrWidth),
    .DataWidth(DataWidth),
    .IdWidth(IdWidth)
  ) slave_dv [NumRsp] (clk);


  for (genvar i=0; i<NumReq; i++) begin : gen_req_if_assignement
    `ACC_ASSIGN(master[i], master_dv[i])
  end

  for (genvar i=0; i<NumRsp; i++) begin : gen_resp_if_assignement
    `ACC_ASSIGN(slave_dv[i], slave[i])
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
  typedef acc_test::acc_slv_monitor #(
    // Acc bus interface paramaters;
    .DataWidth    ( DataWidth        ),
    .AccAddrWidth ( AccAddrWidth     ),
    .IdWidth      ( IdWidth ),
    .NumRsp       ( NumRsp           ),
    .NumReq       ( NumReq           ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) acc_slv_monitor_t;

  typedef acc_test::acc_mst_monitor #(
    // Acc bus interface paramaters;
    .DataWidth    ( DataWidth    ),
    .AccAddrWidth ( AccAddrWidth ),
    .IdWidth      ( IdWidth      ),
    .NumRsp       ( NumRsp       ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) acc_mst_monitor_t;

  // initial begin
    // $monitor("rst_n: %x", rst_n);
  // end

  acc_mst_monitor_t acc_mst_monitor [NumReq];
  for (genvar i=0; i<NumReq; i++) begin : gen_mst_mon
    initial begin
      acc_mst_monitor[i] = new(master_dv[i]);
      @(posedge rst_n);
      acc_mst_monitor[i].monitor();
    end
  end

  acc_slv_monitor_t acc_slv_monitor [NumRsp];
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
  typedef acc_test::rand_acc_slave #(
    // Acc bus interface paramaters;
    .DataWidth    ( DataWidth    ),
    .AccAddrWidth ( AccAddrWidth ),
    .IdWidth      ( IdWidth      ),
    .NumRsp       ( NumRsp       ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) acc_rand_slave_t;

  acc_rand_slave_t rand_acc_slave [NumRsp];
  for (genvar i = 0; i < NumRsp; i++) begin : gen_slv_driver
    initial begin
      rand_acc_slave[i] = new (slave_dv[i]);
      rand_acc_slave[i].reset();
      @(posedge rst_n);
      rand_acc_slave[i].run();
    end
  end

  typedef acc_test::rand_acc_master #(
    // Acc bus interface paramaters;
    .DataWidth    ( DataWidth        ),
    .AccAddrWidth ( AccAddrWidth     ),
    .IdWidth      ( IdWidth          ),
    .NumRsp       ( NumRsp           ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) acc_rand_master_t;

  acc_rand_master_t rand_acc_master [NumReq];

  for (genvar i = 0; i < NumReq; i++) begin
    initial begin
      rand_acc_master[i] = new (master_dv[i]);
      rand_acc_master[i].reset();
      @(posedge rst_n);
      rand_acc_master[i].run(NrRandomTransactions);
    end
  end

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
    automatic int nr_requests=0;
    @(posedge rst_n);
    for (int kk=0; kk<NumReq; kk++) begin // masters k
      automatic int k=kk;
      fork
        for (int ii=0; ii<NumRsp; ii++) begin // slaves i
          fork
            automatic int i=ii;
            forever begin : check_req_path
              automatic tb_req_t req_mst;
              automatic tb_req_t req_slv;
              automatic tb_req_t req_slv_all[NumReq];
              // Master k has sent request to slave i.
              // Check that slave i has received.
              acc_slv_monitor[i].req_mbx[k].get(req_slv);
              acc_mst_monitor[k].req_mbx[i].get(req_mst);
              assert(req_slv.do_compare(req_mst)) else begin
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
                  if (acc_slv_monitor[i].req_mbx[j].num() != 0) begin
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
              // $display("Nr Requests: %d", nr_requests);
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
          automatic tb_rsp_t rsp_mst;
          automatic bit rsp_sender_found;
          acc_mst_monitor[j].rsp_mbx.get(rsp_mst);
          nr_responses++;
          for (int l=0; l<NumRsp; l++) begin
            if (acc_slv_monitor[l].rsp_mbx[j].num() != 0) begin
              automatic tb_rsp_t rsp_slv;
              acc_slv_monitor[l].rsp_mbx[j].peek(rsp_slv);
              if (rsp_slv.do_compare(rsp_mst)) begin
                acc_slv_monitor[l].rsp_mbx[j].get(rsp_slv);
                rsp_sender_found |= 1;
                break;
              end
            end
          end
          assert(rsp_sender_found) else $error( "Response Routing Error");
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
    .NumReq       ( NumReq         ),
    .NumRsp       ( NumRsp         ),
    .AccAddrWidth ( AccAddrWidth   ),
    .DataWidth    ( DataWidth      ),
    .req_t        ( acc_req_t      ),
    .req_chan_t   ( acc_req_chan_t ),
    .rsp_t        ( acc_rsp_t      ),
    .rsp_chan_t   ( acc_rsp_chan_t ),
    .RegisterReq  ( RegisterReq    ),
    .RegisterRsp  ( RegisterRsp    )
  ) dut (
    .clk_i  ( clk    ),
    .rst_ni ( rst_n  ),
    .mst    ( master ),
    .slv    ( slave  )
  );

endmodule
