// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Noam Gallmann <gnoam@live.com>

// Predecoder-compatible definitions of RVB extension instructions

package acc_rvb_insn_pkg;

      parameter unsigned int rvb32_num_insn=67;
      acc_pkg:offl_instr_t rvb32_insn[67];


			acc_rvb_insn[0] =
          '{ instr_data: 32'b 0100000_00000_00000_111_00000_0110011 // ANDN
         instr_mask: 32'b 1111111_00000_00000_111_00000_1111111
         prd_rsp : '{
           p_accept=1'b1,
           p_writeback=1'b1,
           p_use_rs=3'b011
         }
        },
			acc_rvb_insn[1] =
        '{ instr_data: 32'b 0100000_00000_00000_110_00000_0110011, // ORN
        instr_mask: 32'b 1111111_00000_00000_111_00000_1111111,
        prd_rsp : '{
          p_accept = 1'b1,
          p_writeback = 1'b1,
          p_use_rs = 3'b011
        }
      };
			acc_rvb_insn[2] =
          '{ instr_data: 32'b 0100000_00000_00000_100_00000_0110011, // XNOR
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[3] =
          '{ instr_data: 32'b 0010000_00000_00000_010_00000_0110011, // SH1ADD
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[4] =
          '{ instr_data: 32'b 0010000_00000_00000_100_00000_0110011, // SH2ADD
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[5] =
          '{ instr_data: 32'b 0010000_00000_00000_110_00000_0110011, // SH3ADD
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };

			acc_rvb_insn[6] =
          '{ instr_data: 32'b 0000000_00000_00000_001_00000_0110011, // SLL
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[7] =
          '{ instr_data: 32'b 0000000_00000_00000_101_00000_0110011, // SRL
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[8] =
          '{ instr_data: 32'b 0100000_00000_00000_101_00000_0110011, // SRA
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[9] =
          '{ instr_data: 32'b 0010000_00000_00000_001_00000_0110011, // SLO
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[10] =
          '{ instr_data: 32'b 0010000_00000_00000_101_00000_0110011, // SRO
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[11] =
          '{ instr_data: 32'b 0110000_00000_00000_001_00000_0110011, // ROL
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[12] =
          '{ instr_data: 32'b 0110000_00000_00000_101_00000_0110011, // ROR
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };

			acc_rvb_insn[13] =
          '{ instr_data: 32'b 0100100_00000_00000_001_00000_0110011, // SBCLR
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[14] =
          '{ instr_data: 32'b 0010100_00000_00000_001_00000_0110011, // SBSET
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[15] =
          '{ instr_data: 32'b 0110100_00000_00000_001_00000_0110011, // SBINV
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[16] =
          '{ instr_data: 32'b 0100100_00000_00000_101_00000_0110011, // SBEXT
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[17] =
          '{ instr_data: 32'b 0010100_00000_00000_101_00000_0110011, // GORC
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[18] =
          '{ instr_data: 32'b 0110100_00000_00000_101_00000_0110011, // GREV
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };

			acc_rvb_insn[19] =
          '{ instr_data: 32'b 00000_0000000_00000_001_00000_0010011, // SLLI (RV32)
          instr_mask: 32'b 1111_1100000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[20] =
          '{ instr_data: 32'b 00000_0000000_00000_101_00000_0010011, // SRLI (RV32)
          instr_mask: 32'b 1111_1100000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[21] =
          '{ instr_data: 32'b 01000_0000000_00000_101_00000_0010011, // SRAI (RV32)
          instr_mask: 32'b 1111_1100000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[22] =
          '{ instr_data: 32'b 00100_0000000_00000_001_00000_0010011, // SLOI (RV32)
          instr_mask: 32'b 1111_1100000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[23] =
          '{ instr_data: 32'b 00100_0000000_00000_101_00000_0010011, // SROI (RV32)
          instr_mask: 32'b 1111_1100000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[24] =
          '{ instr_data: 32'b 01100_0000000_00000_101_00000_0010011, // RORI (RV32)
          instr_mask: 32'b 1111_1100000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };

			acc_rvb_insn[25] =
          '{ instr_data: 32'b 01001_0000000_00000_001_00000_0010011, // SBCLRI (RV32)
          instr_mask: 32'b 1111_1100000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[26] =
          '{ instr_data: 32'b 00101_0000000_00000_001_00000_0010011, // SBSETI (RV32)
          instr_mask: 32'b 1111_1100000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[27] =
          '{ instr_data: 32'b 01101_0000000_00000_001_00000_0010011, // SBINVI (RV32)
          instr_mask: 32'b 1111_1100000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[28] =
          '{ instr_data: 32'b 01001_0000000_00000_101_00000_0010011, // SBEXTI (RV32)
          instr_mask: 32'b 1111_1100000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[29] =
          '{ instr_data: 32'b 00101_0000000_00000_101_00000_0010011, // GORCI (RV32)
          instr_mask: 32'b 1111_1100000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[30] =
          '{ instr_data: 32'b 01101_0000000_00000_101_00000_0010011, // GREVI (RV32)
          instr_mask: 32'b 1111_1100000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };

			acc_rvb_insn[31] =
          '{ instr_data: 32'b 0000011_00000_00000_001_00000_0110011, // CMIX
          instr_mask: 32'b 000001_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b111
          }
        };
			acc_rvb_insn[32] =
          '{ instr_data: 32'b 0000011_00000_00000_101_00000_0110011, // CMOV
          instr_mask: 32'b 000001_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b111
          }
        };
			acc_rvb_insn[33] =
          '{ instr_data: 32'b 0000010_00000_00000_001_00000_0110011, // FSL
          instr_mask: 32'b 000001_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b111
          }
        };
			acc_rvb_insn[34] =
          '{ instr_data: 32'b 0000010_00000_00000_101_00000_0110011, // FSR
          instr_mask: 32'b 000001_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b111
          }
        };
			acc_rvb_insn[35] =
          '{ instr_data: 32'b 000001_000000_00000_101_00000_0010011, // FSRI (RV32)
          instr_mask: 32'b 00000_100000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b101
          }
        };

			acc_rvb_insn[36] =
          '{ instr_data: 32'b 0110000_00000_00000_001_00000_0010011, // CLZ
          instr_mask: 32'b 111111_11111_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[37] =
          '{ instr_data: 32'b 0110000_00001_00000_001_00000_0010011, // CTZ
          instr_mask: 32'b 111111_11111_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[38] =
          '{ instr_data: 32'b 0110000_00010_00000_001_00000_0010011, // PCNT
          instr_mask: 32'b 111111_11111_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[39] =
          '{ instr_data: 32'b 0110000_00011_00000_001_00000_0010011, // BMATFLIP
          instr_mask: 32'b 111111_11111_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[40] =
          '{ instr_data: 32'b 0110000_00100_00000_001_00000_0010011, // SEXT.B
          instr_mask: 32'b 111111_11111_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[41] =
          '{ instr_data: 32'b 0110000_00101_00000_001_00000_0010011, // SEXT.H
          instr_mask: 32'b 111111_11111_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };

			acc_rvb_insn[42] =
          '{ instr_data: 32'b 0110000_10000_00000_001_00000_0010011, // CRC32.B
          instr_mask: 32'b 111111_11111_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[43] =
          '{ instr_data: 32'b 0110000_10001_00000_001_00000_0010011, // CRC32.H
          instr_mask: 32'b 111111_11111_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[44] =
          '{ instr_data: 32'b 0110000_10010_00000_001_00000_0010011, // CRC32.W
          instr_mask: 32'b 111111_11111_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[45] =
          '{ instr_data: 32'b 0110000_11000_00000_001_00000_0010011, // CRC32C.B
          instr_mask: 32'b 111111_11111_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[46] =
          '{ instr_data: 32'b 0110000_11001_00000_001_00000_0010011, // CRC32C.H
          instr_mask: 32'b 111111_11111_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[47] =
          '{ instr_data: 32'b 0110000_11010_00000_001_00000_0010011, // CRC32C.W
          instr_mask: 32'b 111111_11111_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };

			acc_rvb_insn[48] =
          '{ instr_data: 32'b 0000101_00000_00000_001_00000_0110011, // CLMUL
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[49] =
          '{ instr_data: 32'b 0000101_00000_00000_010_00000_0110011, // CLMULR
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[50] =
          '{ instr_data: 32'b 0000101_00000_00000_011_00000_0110011, // CLMULH
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[51] =
          '{ instr_data: 32'b 0000101_00000_00000_100_00000_0110011, // MIN
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[52] =
          '{ instr_data: 32'b 0000101_00000_00000_101_00000_0110011, // MAX
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[53] =
          '{ instr_data: 32'b 0000101_00000_00000_110_00000_0110011, // MINU
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[54] =
          '{ instr_data: 32'b 0000101_00000_00000_111_00000_0110011, // MAXU
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };

			acc_rvb_insn[55] =
          '{ instr_data: 32'b 0000100_00000_00000_001_00000_0110011, // SHFL
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[56] =
          '{ instr_data: 32'b 0000100_00000_00000_101_00000_0110011, // UNSHFL
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[57] =
          '{ instr_data: 32'b 0100100_00000_00000_110_00000_0110011, // BDEP
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[58] =
          '{ instr_data: 32'b 0000100_00000_00000_110_00000_0110011, // BEXT
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[59] =
          '{ instr_data: 32'b 0000100_00000_00000_100_00000_0110011, // PACK
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[60] =
          '{ instr_data: 32'b 0100100_00000_00000_100_00000_0110011, // PACKU
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[61] =
          '{ instr_data: 32'b 0000100_00000_00000_111_00000_0110011, // PACKH
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[62] =
          '{ instr_data: 32'b 0000100_00000_00000_011_00000_0110011, // BMATOR
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[63] =
          '{ instr_data: 32'b 0100100_00000_00000_011_00000_0110011, // BMATXOR
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };
			acc_rvb_insn[64] =
          '{ instr_data: 32'b 0100100_00000_00000_111_00000_0110011, // BFP
          instr_mask: 32'b 111111_00000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b011
          }
        };

			acc_rvb_insn[65] =
          '{ instr_data: 32'b 000010_000000_00000_001_00000_0010011, // SHFLI (RV32)
          instr_mask: 32'b 11111_110000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };
			acc_rvb_insn[66] =
          '{ instr_data: 32'b 000010_000000_00000_101_00000_0010011, // UNSHFLI (RV32)
          instr_mask: 32'b 11111_110000_00000_111_00000_1111111,
          prd_rsp : '{
            p_accept = 1'b1,
            p_writeback = 1'b1,
            p_use_rs = 3'b001
          }
        };

endpackage

