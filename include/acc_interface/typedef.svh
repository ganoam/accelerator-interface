// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Noam Gallmann <gnoam@live.com>

`ifndef ACC_INTERFACE_TYPEDEF_SVH_
`define ACC_INTERFACE_TYPEDEF_SVH_

`define ACC_TYPEDEF_REQ_CHAN_T(__req_chan_t, __addr_t, __data_t, __id_t) \
  typedef struct packed {                                                \
    __addr_t             addr;                                           \
    __data_t             data_arga;                                      \
    __data_t             data_argb;                                      \
    __data_t             data_argc;                                      \
    logic [31:0]         data_op;                                        \
    __id_t               id;                                             \
  } __req_chan_t;

`define ACC_TYPEDEF_REQ_T(__req_t, __req_chan_t) \
  typedef struct packed {                        \
    __req_chan_t q;                              \
    logic        q_valid;                        \
    logic        p_ready;                        \
  } __req_t;

`define ACC_TYPEDEF_RSP_CHAN_T(__rsp_chan_t, __data_t, __id_t ) \
  typedef struct packed {                                       \
    __data_t data0;                                             \
    __data_t data1;                                             \
    logic    error;                                             \
    logic    dual_writeback;                                    \
    __id_t   id;                                                \
  } __rsp_chan_t;

`define ACC_TYPEDEF_RSP_T(__rsp_t, __rsp_chan_t) \
  typedef struct packed {                        \
    __rsp_chan_t p;                              \
    logic        p_valid;                        \
    logic        q_ready;                        \
  } __rsp_t;

`define ACC_TYPEDEF_ALL(__name, __addr_t, __data_t, __id_t )                \
  `ACC_TYPEDEF_REQ_CHAN_T(__name``_req_chan_t, __addr_t, __data_t, __id_t ) \
  `ACC_TYPEDEF_RSP_CHAN_T(__name``_rsp_chan_t, __data_t, __id_t )           \
  `ACC_TYPEDEF_REQ_T(__name``_req_t, __name``_req_chan_t )                  \
  `ACC_TYPEDEF_RSP_T(__name``_rsp_t,  __name``_rsp_chan_t )

`endif
