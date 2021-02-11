// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Noam Gallmann <gnoam@live.com>

// Macros to assign accelerator interfaces and structs

`ifndef ACC_ASSIGN_SVH_
`define ACC_ASSIGN_SVH_


// Assign handshake.
`define ACC_ASSIGN_VALID(__opt_as, __dst, __src, __chan) \
  __opt_as ``__dst``.``__chan``_valid   = ``__src``.``__chan``_valid;
`define ACC_ASSIGN_READY(__opt_as, __dst, __src, __chan) \
  __opt_as ``__dst``.``__chan``_ready   = ``__src``.``__chan``_ready;

`define ACC_ASSIGN_HANDSHAKE(__opt_as, __dst, __src, __chan) \
  `ACC_ASSIGN_VALID(__opt_as, __dst, __src, __chan)          \
  `ACC_ASSIGN_READY(__opt_as, __src, __dst, __chan)

////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning one ACC interface to another, as if you would do `assign slv =
// mst;`
//
// The channel assignments `ACC_ASSIGN_XX(dst, src)` assign all payload and
// the valid signal of the `XX` channel from the `src` to the `dst` interface
// and they assign the ready signal from the `src` to the `dst` interface. The
// interface assignment `ACC_ASSIGN(dst, src)` assigns all channels including
// handshakes as if `src` was the master of `dst`.
//
// Usage Example: `ACC_ASSIGN(slv, mst) `ACC_ASSIGN_Q(dst, src, aw)
// `ACC_ASSIGN_P(dst, src)
`define ACC_ASSIGN_Q_CHAN(__opt_as, dst, src, __sep_dst, __sep_src)   \
  __opt_as dst.q``__sep_dst``addr      = src.q``__sep_src``addr;      \
  __opt_as dst.q``__sep_dst``data_op   = src.q``__sep_src``data_op;   \
  __opt_as dst.q``__sep_dst``data_arga = src.q``__sep_src``data_arga; \
  __opt_as dst.q``__sep_dst``data_argb = src.q``__sep_src``data_argb; \
  __opt_as dst.q``__sep_dst``data_argc = src.q``__sep_src``data_argc; \
  __opt_as dst.q``__sep_dst``id        = src.q``__sep_src``id;

`define ACC_ASSIGN_P_CHAN(__opt_as, dst, src, __sep_dst, __sep_src) \
  __opt_as dst.p``__sep_dst``data  = src.p``__sep_src``data;        \
  __opt_as dst.p``__sep_dst``error = src.p``__sep_src``error;       \
  __opt_as dst.p``__sep_dst``id = src.p``__sep_src``id;

`define ACC_ASSIGN(slv, mst)                 \
  `ACC_ASSIGN_Q_CHAN(assign, slv, mst, _, _) \
  `ACC_ASSIGN_HANDSHAKE(assign, slv, mst, q) \
  `ACC_ASSIGN_P_CHAN(assign, mst, slv, _, _) \
  `ACC_ASSIGN_HANDSHAKE(assign, mst, slv, p)

////////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning an interface from channel or request/response structs outside a
// process.
//
// The request macro `ACC_ASSIGN_FROM_REQ(acc_if, req_struct)` assigns the
// request channel and the request-side handshake signals of the `acc_if`
// interface from the signals in `req_struct`. The response macro
// `ACC_ASSIGN_FROM_RESP(acc_if, resp_struct)` assigns the response
// channel and the response-side handshake signals of the `acc_if` interface
// from the signals in `resp_struct`.
//
// Usage Example:
// `ACC_ASSIGN_FROM_REQ(my_if, my_req_struct)
`define ACC_ASSIGN_FROM_REQ(acc_if, req_struct)        \
  `ACC_ASSIGN_VALID(assign, acc_if, req_struct, q)     \
  `ACC_ASSIGN_Q_CHAN(assign, acc_if, req_struct, _, .) \
  `ACC_ASSIGN_READY(assign, acc_if, req_struct, p)

`define ACC_ASSIGN_FROM_RESP(acc_if, resp_struct)       \
  `ACC_ASSIGN_READY(assign, acc_if, resp_struct, q)     \
  `ACC_ASSIGN_P_CHAN(assign, acc_if, resp_struct, _, .) \
  `ACC_ASSIGN_VALID(assign, acc_if, resp_struct, p)

////////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning channel or request/response structs from an interface outside a
// process.
//
// The request macro `ACC_ASSIGN_TO_REQ(acc_if, req_struct)` assigns all
// signals of `req_struct` payload and request-side handshake signals to the
// signals in the `acc_if` interface. The response macro
// `ACC_ASSIGN_TO_RESP(acc_if, resp_struct)` assigns all signals of
// `resp_struct` payload and response-side handshake signals to the signals in
// the `acc_if` interface.
//
// Usage Example:
// `ACC_ASSIGN_TO_REQ(my_req_struct, my_if)
`define ACC_ASSIGN_TO_REQ(req_struct, acc_if)          \
  `ACC_ASSIGN_VALID(assign, req_struct, acc_if, q)     \
  `ACC_ASSIGN_Q_CHAN(assign, req_struct, acc_if, ., _) \
  `ACC_ASSIGN_READY(assign, req_struct, acc_if, p)

`define ACC_ASSIGN_TO_RESP(resp_struct, acc_if)         \
  `ACC_ASSIGN_READY(assign, resp_struct, acc_if, q)     \
  `ACC_ASSIGN_P_CHAN(assign, resp_struct, acc_if, ., _) \
  `ACC_ASSIGN_VALID(assign, resp_struct, acc_if, p)

////////////////////////////////////////////////////////////////////////////////////////////////////

`endif
