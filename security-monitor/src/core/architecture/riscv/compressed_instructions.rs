// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::GeneralPurposeRegister;
use crate::error::Error;

// TODO: remove below once riscv_decode supports compressed instructions
pub fn decode_result_register(mtinst: usize) -> Result<GeneralPurposeRegister, Error> {
    use riscv_decode::Instruction::{Lb, Lbu, Ld, Lh, Lhu, Lw, Lwu, Sb, Sd, Sh, Sw};
    let register_index = match riscv_decode::decode(mtinst as u32) {
        Ok(Sb(i)) => Ok(i.rs2()),
        Ok(Sh(i)) => Ok(i.rs2()),
        Ok(Sw(i)) => Ok(i.rs2()),
        Ok(Sd(i)) => Ok(i.rs2()),
        Ok(Lb(i)) => Ok(i.rd()),
        Ok(Lbu(i)) => Ok(i.rd()),
        Ok(Lhu(i)) => Ok(i.rd()),
        Ok(Lwu(i)) => Ok(i.rd()),
        Ok(Lh(i)) => Ok(i.rd()),
        Ok(Lw(i)) => Ok(i.rd()),
        Ok(Ld(i)) => Ok(i.rd()),
        _ => {
            // TODO: do not try to understand what is going on below. Remove all this
            // section once compressed instructions are supported in the
            // rust-decode crate!
            const SH_RS2C: usize = 2;
            const INSN_MATCH_C_LD: usize = 0x6000;
            const INSN_MASK_C_LD: usize = 0xe003;
            const INSN_MATCH_C_SD: usize = 0xe000;
            const INSN_MASK_C_SD: usize = 0xe003;
            const INSN_MATCH_C_LW: usize = 0x4000;
            const INSN_MASK_C_LW: usize = 0xe003;
            const INSN_MATCH_C_SW: usize = 0xc000;
            const INSN_MASK_C_SW: usize = 0xe003;
            const INSN_MATCH_C_LDSP: usize = 0x6002;
            const INSN_MASK_C_LDSP: usize = 0xe003;
            const INSN_MATCH_C_SDSP: usize = 0xe002;
            const INSN_MASK_C_SDSP: usize = 0xe003;
            const INSN_MATCH_C_LWSP: usize = 0x4002;
            const INSN_MASK_C_LWSP: usize = 0xe003;
            const INSN_MATCH_C_SWSP: usize = 0xc002;
            const INSN_MASK_C_SWSP: usize = 0xe003;

            let log_regbytes = 3; // for 64b!
            let shift_right = |x: usize, y: isize| {
                if y < 0 {
                    x << -y
                } else {
                    x >> y
                }
            };
            let reg_mask = (1 << (5 + log_regbytes)) - (1 << log_regbytes);
            let rv_x = |x: usize, s: usize, n: usize| (((x) >> (s)) & ((1 << (n)) - 1));

            if mtinst & INSN_MASK_C_LW == INSN_MATCH_C_LW {
                let index = 8 + rv_x(mtinst, SH_RS2C, 3);
                Ok(index as u32)
            } else if mtinst & INSN_MASK_C_LD == INSN_MATCH_C_LD {
                let index = 8 + rv_x(mtinst, SH_RS2C, 3);
                Ok(index as u32)
            } else if mtinst & INSN_MASK_C_SW == INSN_MATCH_C_SW {
                let tmp_inst = 8 + rv_x(mtinst, SH_RS2C, 3);
                let index = shift_right(tmp_inst, 0isize - log_regbytes as isize) & reg_mask;
                let index = index / 8;
                Ok(index as u32)
            } else if mtinst & INSN_MASK_C_SD == INSN_MATCH_C_SD {
                let tmp_inst = 8 + rv_x(mtinst, SH_RS2C, 3);
                let index = shift_right(tmp_inst, 0isize - log_regbytes as isize) & reg_mask;
                let index = index / 8;
                Ok(index as u32)
            } else if mtinst & INSN_MASK_C_LWSP == INSN_MATCH_C_LWSP {
                Ok(0u32)
            } else if mtinst & INSN_MASK_C_SWSP == INSN_MATCH_C_SWSP {
                let index = shift_right(mtinst, SH_RS2C as isize - log_regbytes as isize) & reg_mask;
                let index = index / 8;
                Ok(index as u32)
            } else if mtinst & INSN_MASK_C_LDSP == INSN_MATCH_C_LDSP {
                Ok(0u32)
            } else if mtinst & INSN_MASK_C_SDSP == INSN_MATCH_C_SDSP {
                let index = shift_right(mtinst, SH_RS2C as isize - log_regbytes as isize) & reg_mask;
                let index = index / 8;
                Ok(index as u32)
            } else {
                Err(Error::InvalidRiscvInstruction(mtinst))
            }
        }
    }?;
    Ok(GeneralPurposeRegister::from_index(register_index as usize).ok_or(Error::InvalidRiscvInstruction(mtinst))?)
}
