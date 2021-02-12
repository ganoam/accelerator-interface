// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

package acc_test;

  import acc_pkg::*;

  class req_t #(
    parameter int AddrWidth    = -1,
    parameter int DataWidth    = -1,
    parameter int IdWidth      = -1
  );
    rand logic [AddrWidth-1:0]    addr;
    rand logic [DataWidth-1:0]    data_arga;
    rand logic [DataWidth-1:0]    data_argb;
    rand logic [DataWidth-1:0]    data_argc;
    rand logic [31:0]             data_op;
    rand logic [IdWidth-1:0]      id;

    typedef req_t # (
      .AddrWidth    ( AddrWidth    ),
      .DataWidth    ( DataWidth    ),
      .IdWidth      ( IdWidth      )
    ) int_req_t;

    task display;
      $display(
              "req.addr: %x\n",       addr,
              "req.data_op: %x\n",    data_op,
              "req.data_arga: %x\n",  data_arga,
              "req.data_argb: %x\n",  data_argb,
              "req.data_argc: %x\n",  data_argc,
              "req.id: %x\n",         id,
              "\n"
            );
    endtask
  endclass

  // Compare reqs of different parameterizations.
  // Within an interconnect, requests may only differ only by IdWidh
  class compare_req #(
    parameter type mst_req_t = logic,
    parameter type slv_req_t = logic
  );
    static function do_compare(mst_req_t mst_req, slv_req_t slv_req);
      return mst_req.addr            == slv_req.addr      &
             mst_req.data_arga       == slv_req.data_arga &
             mst_req.data_argb       == slv_req.data_argb &
             mst_req.data_argc       == slv_req.data_argc &
             mst_req.data_op         == slv_req.data_op   &
             mst_req.id[4:0]       == slv_req.id[4:0];
    endfunction
  endclass


  class rsp_t #(
    parameter int DataWidth    = -1,
    parameter int IdWidth      = -1
  );
    rand logic [DataWidth-1:0] data;
    rand logic                 error;
    logic [IdWidth-1:0]        id;

    typedef rsp_t # (
      .DataWidth    ( DataWidth ),
      .IdWidth      ( IdWidth   )
    ) int_rsp_t;

    task display;
      $display(
              "rsp.data: %x\n"         , data ,
              "rsp.error %x\n"         , error     ,
              "rsp.id: %x\n"           , id,
              "\n"
            );
    endtask
  endclass


  // Compare rsps of different parameterizations.
  // Within an interconnect, requests may only differ only by IdWidh
  class compare_rsp #(
    parameter type mst_rsp_t = logic,
    parameter type slv_rsp_t = logic
  );
    static function do_compare(mst_rsp_t mst_rsp, slv_rsp_t slv_rsp);
      return mst_rsp.data    == slv_rsp.data  &
             mst_rsp.error   == slv_rsp.error &
             mst_rsp.id[4:0] == slv_rsp.id[4:0];
    endfunction
  endclass


  class acc_driver #(
    parameter int AddrWidth    = -1,
    parameter int DataWidth    = -1,
    parameter int IdWidth      = -1,
    parameter int NumRsp       = -1,
    parameter time TA          = 0, // stimuli application time
    parameter time TT          = 0  // stimuli test time
  );

    typedef req_t # (
      .DataWidth    ( DataWidth    ),
      .AddrWidth    ( AddrWidth    ),
      .IdWidth      ( IdWidth      )
    ) int_req_t;

    typedef rsp_t # (
      .DataWidth    ( DataWidth  ),
      .IdWidth      ( IdWidth    )
    ) int_rsp_t;

    virtual ACC_BUS_DV # (
      .DataWidth    ( DataWidth    ),
      .AddrWidth    ( AddrWidth    ),
      .IdWidth      ( IdWidth      )
    ) bus;

    function new(
      virtual ACC_BUS_DV #(
        .DataWidth    ( DataWidth    ),
        .AddrWidth    ( AddrWidth    ),
        .IdWidth      ( IdWidth      )
      ) bus
    );
      this.bus=bus;
    endfunction

    task reset_master;
      bus.q_addr      <= '0;
      bus.q_data_op   <= '0;
      bus.q_data_arga <= '0;
      bus.q_data_argb <= '0;
      bus.q_data_argc <= '0;
      bus.q_id        <= '0;
      bus.q_valid     <= '0;
      bus.p_ready     <= '0;
    endtask

    task reset_slave;
      bus.p_data  <= '0;
      bus.p_id    <= '0;
      bus.p_error <= '0;
      bus.p_valid <= '0;
      bus.q_ready <= '0;
    endtask

    task cycle_start;
      #TT;
    endtask

    task cycle_end;
      @(posedge bus.clk_i);
    endtask

    // Send a request.
    task send_req (input int_req_t req);
      bus.q_addr      <= #TA req.addr;
      bus.q_data_op   <= #TA req.data_op;
      bus.q_data_arga <= #TA req.data_arga;
      bus.q_data_argb <= #TA req.data_argb;
      bus.q_data_argc <= #TA req.data_argc;
      bus.q_id        <= #TA req.id;
      bus.q_valid     <= #TA 1;
      cycle_start();
      while (bus.q_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      bus.q_addr      <= #TA '0;
      bus.q_data_op   <= #TA '0;
      bus.q_data_arga <= #TA '0;
      bus.q_data_argb <= #TA '0;
      bus.q_data_argc <= #TA '0;
      bus.q_id        <= #TA '0;
      bus.q_valid     <= #TA  0;
    endtask

    // Send a response.
    task send_rsp(input int_rsp_t rsp);
      bus.p_data  <= #TA rsp.data;
      bus.p_id    <= #TA rsp.id;
      bus.p_error <= #TA rsp.error;
      bus.p_valid <= #TA 1;
      cycle_start();
      while (bus.p_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      bus.p_data  <= #TA '0;
      bus.p_id    <= #TA '0;
      bus.p_error <= #TA '0;
      bus.p_valid <= #TA 0;
    endtask

    // Receive a request.
    task recv_req (output int_req_t req);
      bus.q_ready <= #TA 1;
      cycle_start();
      while (bus.q_valid != 1) begin cycle_end(); cycle_start(); end
      req = new;
      req.addr      = bus.q_addr;
      req.data_op   = bus.q_data_op;
      req.data_arga = bus.q_data_arga;
      req.data_argb = bus.q_data_argb;
      req.data_argc = bus.q_data_argc;
      req.id        = bus.q_id;
      cycle_end();
      bus.q_ready <= #TA 0;
    endtask

    // Receive a response.
    task recv_rsp (output int_rsp_t rsp);
      bus.p_ready <= #TA 1;
      cycle_start();
      while (bus.p_valid != 1) begin cycle_end(); cycle_start(); end
      rsp       = new;
      rsp.data  = bus.p_data;
      rsp.error = bus.p_error;
      rsp.id    = bus.p_id;
      cycle_end();
      bus.p_ready <= #TA 0;
    endtask

    // Monitor request
    task mon_req (output int_req_t req);
      cycle_start();
      while (!(bus.q_valid && bus.q_ready)) begin cycle_end(); cycle_start(); end
      req = new;
      req.addr      = bus.q_addr;
      req.data_op   = bus.q_data_op;
      req.data_arga = bus.q_data_arga;
      req.data_argb = bus.q_data_argb;
      req.data_argc = bus.q_data_argc;
      req.id        = bus.q_id;
      cycle_end();
    endtask

    // Monitor response.
    task mon_rsp (output int_rsp_t rsp);
      cycle_start();
      while (!(bus.p_valid &&bus.p_ready)) begin cycle_end(); cycle_start(); end
      rsp       = new;
      rsp.data  = bus.p_data;
      rsp.error = bus.p_error;
      rsp.id    = bus.p_id;
      cycle_end();
    endtask

  endclass

  // Super classes for random acc drivers
  virtual class rand_acc #(
    // Acc interface parameters
    parameter int DataWidth    = -1,
    parameter int AddrWidth    = -1,
    parameter int IdWidth      = -1,
    parameter int NumRsp       = -1, // TODO: Remove unused parameter

    // Stimuli application and test time
    parameter time TA = 0ps,
    parameter time TT = 0ps
  );

    typedef req_t #(
      .AddrWidth    ( AddrWidth    ),
      .DataWidth    ( DataWidth    ),
      .IdWidth      ( IdWidth      )
    ) int_req_t;

    typedef rsp_t #(
      .DataWidth    ( DataWidth  ),
      .IdWidth      ( IdWidth    )
    ) int_rsp_t;

    typedef acc_test::acc_driver #(
      // Acc interface parameters
      .AddrWidth    ( AddrWidth    ),
      .DataWidth    ( DataWidth    ),
      .IdWidth      ( IdWidth      ),
      // Stimuli application and test time
      .TA(TA),
      .TT(TT)
    ) acc_driver_t;

    acc_driver_t drv;

    function new(
      virtual ACC_BUS_DV #(
        .DataWidth    ( DataWidth    ),
        .AddrWidth    ( AddrWidth    ),
        .IdWidth      ( IdWidth      )
      ) bus );
      this.drv = new (bus);
    endfunction

    task automatic rand_wait(input int unsigned min, input int unsigned max);
      int unsigned rand_success, cycles;
      rand_success = std::randomize(cycles) with {
        cycles >= min;
        cycles <= max;
        // Weigh the distribution so that the minimum cycle time is the common
        // case.
        cycles dist {min := 10, [min+1:max] := 1};
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat (cycles) @(posedge this.drv.bus.clk_i);
    endtask

  endclass

  // Generate random requests as a master device.
  class rand_acc_master #(
    // Acc interface parameters
    parameter int DataWidth       = -1,
    parameter int AccAddrWidth    = -1,
    parameter int HierAddrWidth   = -1,
    parameter int IdWidth         = -1,
    parameter int NumHier         = -1,
    parameter int NumRsp[NumHier] = '{-1},
    // Stimuli application and test time
    parameter time         TA                  = 0ps,
    parameter time         TT                  = 0ps,
    parameter int unsigned REQ_MIN_WAIT_CYCLES = 1,
    parameter int unsigned REQ_MAX_WAIT_CYCLES = 20,
    parameter int unsigned RSP_MIN_WAIT_CYCLES = 1,
    parameter int unsigned RSP_MAX_WAIT_CYCLES = 20
  ) extends rand_acc #(
      // Acc interface parameters
      .AddrWidth ( AccAddrWidth + HierAddrWidth ),
      .DataWidth ( DataWidth                    ),
      .IdWidth   ( IdWidth                      ),
      // Stimuli application and test time
      .TA(TA),
      .TT(TT)
    );

    int unsigned cnt = 0;
    bit req_done = 0;

    // Reset the driver.
    task reset();
      drv.reset_master();
    endtask

    // Constructor.
    function new (
      virtual ACC_BUS_DV #(
        .DataWidth ( DataWidth                    ),
        .AddrWidth ( AccAddrWidth + HierAddrWidth ),
        .IdWidth   ( IdWidth                      )
      ) bus );
      super.new(bus);
    endfunction

    task run(input int n);
      fork
        send_requests(n);
        recv_response();
      join
    endtask

    // Send random requests.
    task send_requests (input int n);
      automatic int_req_t req = new;

      repeat (n) begin
        this.cnt++;
        assert(req.randomize with
          {
            addr[AddrWidth-1:AccAddrWidth] inside {[0:NumHier-1]};
            addr[AccAddrWidth-1:0]         inside {[0:NumRsp[addr[AddrWidth-1:AccAddrWidth]]-1]};
          }
        );
        rand_wait(REQ_MIN_WAIT_CYCLES, REQ_MAX_WAIT_CYCLES);
        this.drv.send_req(req);
      end
      this.req_done = 1;
    endtask

    // Receive random responses.
    // TODO: This won't stop until a response has been sent for all requests.
    //       We do not require that.
    task recv_response;
      while (!this.req_done || this.cnt > 0) begin
        automatic int_rsp_t rsp;
        this.cnt--;
        rand_wait(RSP_MIN_WAIT_CYCLES, RSP_MAX_WAIT_CYCLES);
        this.drv.recv_rsp(rsp);
      end
    endtask
  endclass

  class rand_acc_slave #(
    // Acc interface parameters
    parameter int AddrWidth    = -1,
    parameter int DataWidth    = -1,
    parameter int IdWidth      = -1,
    parameter int NumRsp       = -1,
    parameter int NumReq       = -1,
    // Stimuli application and test time
    parameter time  TA = 0ps,
    parameter time  TT = 0ps,
    parameter int unsigned REQ_MIN_WAIT_CYCLES = 0,
    parameter int unsigned REQ_MAX_WAIT_CYCLES = 10,
    parameter int unsigned RSP_MIN_WAIT_CYCLES = 0,
    parameter int unsigned RSP_MAX_WAIT_CYCLES = 10
  ) extends rand_acc #(
      // Acc interface parameters
      .AddrWidth ( AddrWidth ),
      .DataWidth ( DataWidth ),
      .IdWidth   ( IdWidth   ),
      .NumRsp    ( NumRsp    ),
      // Stimuli application and test time
      .TA(TA),
      .TT(TT)
    );

    mailbox req_mbx[NumReq];

    /// Reset the driver.
    task reset();
      drv.reset_slave();
    endtask

    task run();
      fork
        recv_requests();
        send_responses();
      join
    endtask

    /// Constructor.
    function new (
      virtual ACC_BUS_DV #(
        .DataWidth    ( DataWidth    ),
        .AddrWidth    ( AddrWidth    ),
        .IdWidth      ( IdWidth      )
      ) bus);
      super.new(bus);
      foreach(this.req_mbx[ii]) req_mbx[ii] = new();
    endfunction

    task recv_requests();
      forever begin
        automatic int_req_t req;
        rand_wait(REQ_MIN_WAIT_CYCLES, REQ_MAX_WAIT_CYCLES);
        this.drv.recv_req(req);
        req_mbx[req.id[IdWidth-1:5]].put(req);
      end
    endtask

    task send_responses();
      forever begin
        automatic int_rsp_t rsp = new;
        automatic int_req_t req;
        // generate random sequence of requesters.
        automatic int req_id[NumReq];
        automatic bit req_found = 1'b0;
        for (int i =0; i<NumReq; i++) begin
          req_id[i] = i;
        end
        req_id.shuffle();
        // Try to respond to first requester. If mbx is empty, try next.
        for (int i=0; i<NumReq; i++) begin
          automatic int r_id = req_id[i];
          if (req_mbx[r_id].num() != 0) begin
            req_mbx[r_id].get(req);
            req_found = 1'b1;
            break;
          end
        end
        if (req_found==1'b1) begin
          assert(rsp.randomize());
          rsp.id = req.id;

          // send response back to requester.
          @(posedge this.drv.bus.clk_i);
          rand_wait(RSP_MIN_WAIT_CYCLES, RSP_MAX_WAIT_CYCLES);
          this.drv.send_rsp(rsp);
        end else begin
          this.drv.cycle_end();
        end
      end
    endtask
  endclass

  class acc_slv_monitor #(
    // Acc interface parameters
    parameter int DataWidth    = -1,
    parameter int AddrWidth    = -1,
    parameter int IdWidth      = -1,
    parameter int NumReq       = -1,
    parameter int NumRsp       = -1,
    // Stimuli application and test time
    parameter time  TA = 0ps,
    parameter time  TT = 0ps
  ) extends rand_acc #(
        .DataWidth    ( DataWidth    ),
        .AddrWidth    ( AddrWidth    ),
        .IdWidth      ( IdWidth      ),
        .NumRsp       ( NumRsp       ),
        .TA           ( TA           ),
        .TT           ( TT           )
  );

    mailbox req_mbx[NumReq];
    mailbox rsp_mbx[NumReq];

    // Constructor.
    function new (
      virtual ACC_BUS_DV #(
        .DataWidth    ( DataWidth    ),
        .AddrWidth    ( AddrWidth    ),
        .IdWidth      ( IdWidth      )
      ) bus);
      super.new(bus);
      foreach (this.req_mbx[ii]) req_mbx[ii] = new();
      foreach (this.rsp_mbx[ii]) rsp_mbx[ii] = new();

    endfunction

    // Slave Monitor.
    // For each master maintain a separate mailbox.
    task monitor;
      fork
        forever begin
          automatic int_req_t req;
          this.drv.mon_req(req);
          // put in req mbox corresponding to the requester
          req_mbx[req.id[IdWidth-1:5]].put(req);
        end
        forever begin
          automatic int_rsp_t rsp;
          this.drv.mon_rsp(rsp);
          // put in req mbox corresponding to the requester
          rsp_mbx[rsp.id[IdWidth-1:5]].put(rsp);
        end
      join
    endtask
  endclass

  class acc_mst_monitor #(
    // Acc interface parameters
    parameter int DataWidth    = -1,
    parameter int AddrWidth    = -1,
    parameter int NumRsp       = -1,
    parameter int IdWidth      = -1,
    // Stimuli application and test time
    parameter time  TA = 0ps,
    parameter time  TT = 0ps
  ) extends rand_acc #(
        .DataWidth    ( DataWidth    ),
        .AddrWidth    ( AddrWidth    ),
        .IdWidth      ( IdWidth      ),
        .NumRsp       ( NumRsp       ),
        .TA           ( TA           ),
        .TT           ( TT           )
    );

    // TODO: Too many mailboxes. Only need NumRsp, but difficult to reduce.
    // Also change accordingly: mark XXX
    mailbox req_mbx [AddrWidth**2];
    mailbox rsp_mbx = new;

    // Constructor.
    function new (
      virtual ACC_BUS_DV #(
        .DataWidth    ( DataWidth    ),
        .AddrWidth    ( AddrWidth    ),
        .IdWidth      ( IdWidth      )
      ) bus);
      super.new(bus);
      foreach (this.req_mbx[ii]) req_mbx[ii] = new;
    endfunction

    // Master Monitor.
    // For each slave maintain a separate mailbox.
    task monitor;
      fork
        forever begin
          automatic int_req_t req;
          this.drv.mon_req(req);
          // put in req mbox corresponding to the responder
          req_mbx[req.addr].put(req);
        end
        forever begin
          automatic int_rsp_t rsp;
          this.drv.mon_rsp(rsp);
          rsp_mbx.put(rsp);
        end
      join
    endtask
  endclass

endpackage
