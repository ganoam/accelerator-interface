// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

package acc_test;

  import acc_pkg::*;

  class req_t #(
    parameter int AccAddrWidth = -1,
    parameter int DataWidth    = -1,
    parameter int NumRsp       = -1,
    parameter int IdWidth      = -1
  );
    rand logic [AccAddrWidth-1:0] addr;
    rand logic [DataWidth-1:0]    data_arga;
    rand logic [DataWidth-1:0]    data_argb;
    rand logic [DataWidth-1:0]    data_argc;
    rand logic [31:0]             data_op;
    rand logic [4:0]              rd_id;
    rand logic [IdWidth-1:0]      req_id;

    constraint legal_acc_addr_c {
      addr inside {[0:NumRsp-1]};
    }

    typedef req_t # (
      .AccAddrWidth ( AccAddrWidth ),
      .DataWidth    ( DataWidth    ),
      .IdWidth      ( IdWidth      ),
      .NumRsp       ( NumRsp       )
    ) int_req_t;

    // Compare objects of the same type
    function do_compare(int_req_t rhs);
      return data_arga == rhs.data_arga &
             data_argb == rhs.data_argb &
             data_argc == rhs.data_argc &
             data_op   == rhs.data_o-p   &
             rd_id     == rhs.rd_id;
             // not testing request ID, as not set at time of sending.
             // req_id    == rhs.req_id;
             // not testing address, as not relevant after xbar.
             // addr      == rhs.addr      &
    endfunction

    task display;
      $display(
              "req.addr: %x\n",      addr,
              "req.data_op: %x\n",   data_op,
              "req.data_arga: %x\n", data_arga,
              "req.data_argb: %x\n", data_argb,
              "req.data_argc: %x\n", data_argc,
              "req.rd_id: %x\n",     rd_id,
              "req.req_id: %x\n",    req_id,
              "\n"
            );
    endtask

  endclass

  class rsp_t #(
    parameter int DataWidth    = -1,
    parameter int IdWidth      = -1
  );
    rand logic [DataWidth-1:0] data;
    rand logic                 error;
    logic [4:0]                rd_id;
    logic [IdWidth-1:0]        req_id;

    typedef rsp_t # (
      .DataWidth    ( DataWidth ),
      .IdWidth      ( IdWidth   )
    ) int_rsp_t;

    // Compare objects of the same type
    function do_compare(int_rsp_t rhs);
      return data   == rhs.data   &
             error  == rhs.error  &
             req_id == rhs.req_id &
             rd_id  == rhs.rd_id;
    endfunction

    task display;
      $display(
              "rsp.data: %x\n",   data,
              "rsp.error %x\n",   error,
              "rsp.rd_id: %x\n",  rd_id,
              "rsp.req_id: %x\n", req_id,
              "\n"
            );
    endtask

  endclass

  class acc_driver #(
    parameter int AccAddrWidth = -1,
    parameter int DataWidth    = -1,
    parameter int IdWidth      = -1,
    parameter int NumRsp       = -1,
    parameter time TA          = 0, // stimuli application time
    parameter time TT          = 0  // stimuli test time
  );

    typedef req_t # (
      .AccAddrWidth ( AccAddrWidth ),
      .DataWidth    ( DataWidth    ),
      .IdWidth      ( IdWidth      ),
      .NumRsp       ( NumRsp       )
    ) int_req_t;

    typedef rsp_t # (
      .DataWidth    ( DataWidth ),
      .IdWidth      ( IdWidth   )
    ) int_rsp_t;

    virtual ACC_BUS_DV # (
      .DataWidth         ( DataWidth    ),
      .AccAddrWidth      ( AccAddrWidth ),
      .IdWidth           ( IdWidth      )
    ) bus;

    function new(
      virtual ACC_BUS_DV #(

        .DataWidth    ( DataWidth    ),
        .AccAddrWidth ( AccAddrWidth ),
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
      bus.q_rd_id     <= '0;
      bus.q_req_id    <= '0;
      bus.q_valid     <= '0;
      bus.p_ready     <= '0;
    endtask

    task reset_slave;
      bus.p_data   <= '0;
      bus.p_rd_id  <= '0;
      bus.p_req_id <= '0;
      bus.p_error  <= '0;
      bus.p_valid  <= '0;
      bus.q_ready  <= '0;
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
      bus.q_req_id    <= #TA req.req_id;
      bus.q_rd_id     <= #TA req.rd_id;
      bus.q_valid     <= #TA 1;
      cycle_start();
      while (bus.q_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      bus.q_addr      <= #TA '0;
      bus.q_data_op   <= #TA '0;
      bus.q_data_arga <= #TA '0;
      bus.q_data_argb <= #TA '0;
      bus.q_data_argc <= #TA '0;
      bus.q_req_id    <= #TA '0;
      bus.q_rd_id     <= #TA '0;
      bus.q_valid     <= #TA  0;
    endtask

    // Send a response.
    task send_rsp(input int_rsp_t rsp);
      bus.p_data   <= #TA rsp.data;
      bus.p_req_id <= #TA rsp.req_id;
      bus.p_rd_id  <= #TA rsp.rd_id;
      bus.p_error  <= #TA rsp.error;
      bus.p_valid  <= #TA 1;
      cycle_start();
      while (bus.p_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      bus.p_data   <= #TA '0;
      bus.p_req_id <= #TA '0;
      bus.p_rd_id  <= #TA '0;
      bus.p_error  <= #TA '0;
      bus.p_valid  <= #TA 0;
    endtask

    // Receive a request.
    task recv_req (output int_req_t req);
      bus.q_ready <= #TA 1;
      cycle_start();
      while (bus.q_valid != 1) begin cycle_end(); cycle_start(); end
      req           = new;
      req.addr      = bus.q_addr;
      req.data_op   = bus.q_data_op;
      req.data_arga = bus.q_data_arga;
      req.data_argb = bus.q_data_argb;
      req.data_argc = bus.q_data_argc;
      req.req_id    = bus.q_req_id;
      req.rd_id     = bus.q_rd_id;
      cycle_end();
      bus.q_ready <= #TA 0;
    endtask

    // Receive a response.
    task recv_rsp (output int_rsp_t rsp);
      bus.p_ready <= #TA 1;
      cycle_start();
      while (bus.p_valid != 1) begin cycle_end(); cycle_start(); end
      rsp        = new;
      rsp.data   = bus.p_data;
      rsp.error  = bus.p_error;
      rsp.req_id = bus.p_req_id;
      rsp.rd_id  = bus.p_rd_id;
      cycle_end();
      bus.p_ready <= #TA 0;
    endtask

    // Monitor request
    task mon_req (output int_req_t req);
      cycle_start();
      while (!(bus.q_valid && bus.q_ready)) begin cycle_end(); cycle_start(); end
      req           = new;
      req.addr      = bus.q_addr;
      req.data_op   = bus.q_data_op;
      req.data_arga = bus.q_data_arga;
      req.data_argb = bus.q_data_argb;
      req.data_argc = bus.q_data_argc;
      req.req_id    = bus.q_req_id;
      req.rd_id     = bus.q_rd_id;
      cycle_end();
    endtask

    // Monitor response.
    task mon_rsp (output int_rsp_t rsp);
      cycle_start();
      while (!(bus.p_valid &&bus.p_ready)) begin cycle_end(); cycle_start(); end
      rsp        = new;
      rsp.data   = bus.p_data;
      rsp.error  = bus.p_error;
      rsp.req_id = bus.p_req_id;
      rsp.rd_id  = bus.p_rd_id;
      cycle_end();
    endtask

  endclass

  // Super classes for random acc drivers
  virtual class rand_acc #(
    // Acc interface parameters
    parameter int DataWidth       = -1,
    parameter int AccAddrWidth    = -1,
    parameter int IdWidth         = -1,
    parameter int NumRsp          = -1,

    // Stimuli application and test time
    parameter time TA = 0ps,
    parameter time TT = 0ps
  );

    typedef req_t #(
      .AccAddrWidth ( AccAddrWidth ),
      .DataWidth    ( DataWidth    ),
      .IdWidth      ( IdWidth      ),
      .NumRsp       ( NumRsp       )
    ) int_req_t;

    typedef rsp_t #(
      .DataWidth    ( DataWidth ),
      .IdWidth      ( IdWidth   )
    ) int_rsp_t;

    typedef acc_test::acc_driver #(
      // Acc interface parameters
      .AccAddrWidth ( AccAddrWidth ),
      .DataWidth    ( DataWidth    ),
      .IdWidth      ( IdWidth      ),
      .NumRsp       ( NumRsp       ),
      // Stimuli application and test time
      .TA(TA),
      .TT(TT)
    ) acc_driver_t;

    acc_driver_t drv;

    function new(
      virtual ACC_BUS_DV #(
        .DataWidth    ( DataWidth    ),
        .AccAddrWidth ( AccAddrWidth ),
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
    parameter int DataWidth    = -1,
    parameter int AccAddrWidth = -1,
    parameter int IdWidth      = -1,
    parameter int NumRsp       = -1,
    // Stimuli application and test time
    parameter time         TA                  = 0ps,
    parameter time         TT                  = 0ps,
    parameter int unsigned REQ_MIN_WAIT_CYCLES = 1,
    parameter int unsigned REQ_MAX_WAIT_CYCLES = 20,
    parameter int unsigned RSP_MIN_WAIT_CYCLES = 1,
    parameter int unsigned RSP_MAX_WAIT_CYCLES = 20
  ) extends rand_acc #(
      // Acc interface parameters
      .AccAddrWidth ( AccAddrWidth ),
      .DataWidth    ( DataWidth    ),
      .IdWidth      ( IdWidth      ),
      .NumRsp       ( NumRsp       ),
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
        .DataWidth    ( DataWidth    ),
        .AccAddrWidth ( AccAddrWidth ),
        .IdWidth      ( IdWidth      )
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
      automatic int_req_t r = new;

      repeat (n) begin
        this.cnt++;
        assert(r.randomize());
        rand_wait(REQ_MIN_WAIT_CYCLES, REQ_MAX_WAIT_CYCLES);
        this.drv.send_req(r);
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
    parameter int AccAddrWidth = -1,
    parameter int DataWidth    = -1,
    parameter int IdWidth      = -1,
    parameter int NumRsp       = -1,
    // Stimuli application and test time
    parameter time  TA = 0ps,
    parameter time  TT = 0ps,
    parameter int unsigned REQ_MIN_WAIT_CYCLES = 0,
    parameter int unsigned REQ_MAX_WAIT_CYCLES = 10,
    parameter int unsigned RSP_MIN_WAIT_CYCLES = 0,
    parameter int unsigned RSP_MAX_WAIT_CYCLES = 10
  ) extends rand_acc #(
      // Acc interface parameters
      .AccAddrWidth ( AccAddrWidth ),
      .DataWidth    ( DataWidth    ),
      .IdWidth      ( IdWidth      ),
      .NumRsp       ( NumRsp       ),
      // Stimuli application and test time
      .TA(TA),
      .TT(TT)
    );

    mailbox req_mbx = new();

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
        .DataWidth(DataWidth),
        .AccAddrWidth(AccAddrWidth),
        .IdWidth(IdWidth)
      ) bus);
      super.new(bus);
    endfunction

    task recv_requests();
      forever begin
        automatic int_req_t req;
        rand_wait(REQ_MIN_WAIT_CYCLES, REQ_MAX_WAIT_CYCLES);
        this.drv.recv_req(req);
        req_mbx.put(req);
      end
    endtask

    task send_responses();
      forever begin
        automatic int_rsp_t rsp = new;
        automatic int_req_t req;
        // $display("Sending Response");
        req_mbx.get(req);
        assert(rsp.randomize());
        // send response back to requester.
        rsp.req_id = req.req_id;
        rsp.rd_id  = req.rd_id;

        @(posedge this.drv.bus.clk_i);
        rand_wait(RSP_MIN_WAIT_CYCLES, RSP_MAX_WAIT_CYCLES);
        this.drv.send_rsp(rsp);
      end
    endtask
  endclass

  class acc_slv_monitor #(
    // Acc interface parameters
    parameter int DataWidth       = -1,
    parameter int AccAddrWidth    = -1,
    parameter int IdWidth         = -1,
    parameter int NumReq          = -1,
    parameter int NumRsp          = -1,
    // Stimuli application and test time
    parameter time  TA = 0ps,
    parameter time  TT = 0ps
  ) extends rand_acc #(
        .DataWidth    ( DataWidth    ),
        .AccAddrWidth ( AccAddrWidth ),
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
        .DataWidth(DataWidth),
        .AccAddrWidth(AccAddrWidth),
        .IdWidth(IdWidth)
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
          // put in req mbox corresponding to the sending requester
          req_mbx[req.req_id].put(req);
        end
        forever begin
          automatic int_rsp_t rsp;
          this.drv.mon_rsp(rsp);
          // put in rsp mbox corresponding to the receiving requester
          rsp_mbx[rsp.req_id].put(rsp);
        end
      join
    endtask
  endclass

  class acc_mst_monitor #(
    // Acc interface parameters
    parameter int unsigned DataWidth    =-1,
    parameter int unsigned AccAddrWidth =-1,
    parameter int unsigned IdWidth      =-1,
    parameter int unsigned NumRsp       =-1,
    // Stimuli application and test time
    parameter time  TA = 0ps,
    parameter time  TT = 0ps
  ) extends rand_acc #(
        .DataWidth    ( DataWidth    ),
        .AccAddrWidth ( AccAddrWidth ),
        .IdWidth      ( IdWidth      ),
        .NumRsp       ( NumRsp       ),
        .TA           ( TA           ),
        .TT           ( TT           )
    );

    mailbox req_mbx [NumRsp];
    mailbox rsp_mbx = new;

    // Constructor.
    function new (
      //$display("blubb");
      virtual ACC_BUS_DV #(
        .DataWidth    ( DataWidth    ),
        .AccAddrWidth ( AccAddrWidth ),
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

