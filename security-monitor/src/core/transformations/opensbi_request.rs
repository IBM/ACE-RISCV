// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::hart::{GpRegister, HartState};

pub struct OpensbiRequest {
    pub regs: opensbi_sys::sbi_trap_regs,
}

impl OpensbiRequest {
    pub fn new(hart_state: &HartState) -> Self {
        Self {
            regs: opensbi_sys::sbi_trap_regs {
                zero: 0,
                ra: hart_state.gpr(GpRegister::ra).try_into().unwrap_or(0),
                sp: hart_state.gpr(GpRegister::sp).try_into().unwrap_or(0),
                gp: hart_state.gpr(GpRegister::gp).try_into().unwrap_or(0),
                tp: hart_state.gpr(GpRegister::tp).try_into().unwrap_or(0),
                t0: hart_state.gpr(GpRegister::t0).try_into().unwrap_or(0),
                t1: hart_state.gpr(GpRegister::t1).try_into().unwrap_or(0),
                t2: hart_state.gpr(GpRegister::t2).try_into().unwrap_or(0),
                s0: hart_state.gpr(GpRegister::s0).try_into().unwrap_or(0),
                s1: hart_state.gpr(GpRegister::s1).try_into().unwrap_or(0),
                a0: hart_state.gpr(GpRegister::a0).try_into().unwrap_or(0),
                a1: hart_state.gpr(GpRegister::a1).try_into().unwrap_or(0),
                a2: hart_state.gpr(GpRegister::a2).try_into().unwrap_or(0),
                a3: hart_state.gpr(GpRegister::a3).try_into().unwrap_or(0),
                a4: hart_state.gpr(GpRegister::a4).try_into().unwrap_or(0),
                a5: hart_state.gpr(GpRegister::a5).try_into().unwrap_or(0),
                a6: hart_state.gpr(GpRegister::a6).try_into().unwrap_or(0),
                a7: hart_state.gpr(GpRegister::a7).try_into().unwrap_or(0),
                s2: hart_state.gpr(GpRegister::s2).try_into().unwrap_or(0),
                s3: hart_state.gpr(GpRegister::s3).try_into().unwrap_or(0),
                s4: hart_state.gpr(GpRegister::s4).try_into().unwrap_or(0),
                s5: hart_state.gpr(GpRegister::s5).try_into().unwrap_or(0),
                s6: hart_state.gpr(GpRegister::s6).try_into().unwrap_or(0),
                s7: hart_state.gpr(GpRegister::s7).try_into().unwrap_or(0),
                s8: hart_state.gpr(GpRegister::s8).try_into().unwrap_or(0),
                s9: hart_state.gpr(GpRegister::s9).try_into().unwrap_or(0),
                s10: hart_state.gpr(GpRegister::s10).try_into().unwrap_or(0),
                s11: hart_state.gpr(GpRegister::s11).try_into().unwrap_or(0),
                t3: hart_state.gpr(GpRegister::t3).try_into().unwrap_or(0),
                t4: hart_state.gpr(GpRegister::t4).try_into().unwrap_or(0),
                t5: hart_state.gpr(GpRegister::t5).try_into().unwrap_or(0),
                t6: hart_state.gpr(GpRegister::t6).try_into().unwrap_or(0),
                mepc: hart_state.mepc.try_into().unwrap_or(0),
                mstatus: hart_state.mstatus.try_into().unwrap_or(0),
                // TODO: mstatusH exists only in rv32. Adjust this to support rv32
                mstatusH: 0,
            },
        }
    }
}
