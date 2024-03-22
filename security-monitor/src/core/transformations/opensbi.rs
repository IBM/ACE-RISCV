// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GeneralPurposeRegister, HartArchitecturalState};
use crate::core::control_data::HardwareHart;

#[derive(Debug)]
pub struct OpensbiRequest {
    regs: opensbi_sys::sbi_trap_regs,
}

impl OpensbiRequest {
    pub fn from_hardware_hart(hardware_hart: &HardwareHart) -> Self {
        Self {
            regs: opensbi_sys::sbi_trap_regs {
                zero: 0,
                ra: hardware_hart.gprs().read(GeneralPurposeRegister::ra).try_into().unwrap_or(0),
                sp: hardware_hart.gprs().read(GeneralPurposeRegister::sp).try_into().unwrap_or(0),
                gp: hardware_hart.gprs().read(GeneralPurposeRegister::gp).try_into().unwrap_or(0),
                tp: hardware_hart.gprs().read(GeneralPurposeRegister::tp).try_into().unwrap_or(0),
                t0: hardware_hart.gprs().read(GeneralPurposeRegister::t0).try_into().unwrap_or(0),
                t1: hardware_hart.gprs().read(GeneralPurposeRegister::t1).try_into().unwrap_or(0),
                t2: hardware_hart.gprs().read(GeneralPurposeRegister::t2).try_into().unwrap_or(0),
                s0: hardware_hart.gprs().read(GeneralPurposeRegister::s0).try_into().unwrap_or(0),
                s1: hardware_hart.gprs().read(GeneralPurposeRegister::s1).try_into().unwrap_or(0),
                a0: hardware_hart.gprs().read(GeneralPurposeRegister::a0).try_into().unwrap_or(0),
                a1: hardware_hart.gprs().read(GeneralPurposeRegister::a1).try_into().unwrap_or(0),
                a2: hardware_hart.gprs().read(GeneralPurposeRegister::a2).try_into().unwrap_or(0),
                a3: hardware_hart.gprs().read(GeneralPurposeRegister::a3).try_into().unwrap_or(0),
                a4: hardware_hart.gprs().read(GeneralPurposeRegister::a4).try_into().unwrap_or(0),
                a5: hardware_hart.gprs().read(GeneralPurposeRegister::a5).try_into().unwrap_or(0),
                a6: hardware_hart.gprs().read(GeneralPurposeRegister::a6).try_into().unwrap_or(0),
                a7: hardware_hart.gprs().read(GeneralPurposeRegister::a7).try_into().unwrap_or(0),
                s2: hardware_hart.gprs().read(GeneralPurposeRegister::s2).try_into().unwrap_or(0),
                s3: hardware_hart.gprs().read(GeneralPurposeRegister::s3).try_into().unwrap_or(0),
                s4: hardware_hart.gprs().read(GeneralPurposeRegister::s4).try_into().unwrap_or(0),
                s5: hardware_hart.gprs().read(GeneralPurposeRegister::s5).try_into().unwrap_or(0),
                s6: hardware_hart.gprs().read(GeneralPurposeRegister::s6).try_into().unwrap_or(0),
                s7: hardware_hart.gprs().read(GeneralPurposeRegister::s7).try_into().unwrap_or(0),
                s8: hardware_hart.gprs().read(GeneralPurposeRegister::s8).try_into().unwrap_or(0),
                s9: hardware_hart.gprs().read(GeneralPurposeRegister::s9).try_into().unwrap_or(0),
                s10: hardware_hart.gprs().read(GeneralPurposeRegister::s10).try_into().unwrap_or(0),
                s11: hardware_hart.gprs().read(GeneralPurposeRegister::s11).try_into().unwrap_or(0),
                t3: hardware_hart.gprs().read(GeneralPurposeRegister::t3).try_into().unwrap_or(0),
                t4: hardware_hart.gprs().read(GeneralPurposeRegister::t4).try_into().unwrap_or(0),
                t5: hardware_hart.gprs().read(GeneralPurposeRegister::t5).try_into().unwrap_or(0),
                t6: hardware_hart.gprs().read(GeneralPurposeRegister::t6).try_into().unwrap_or(0),
                mepc: hardware_hart.csrs().mepc.read_value().try_into().unwrap_or(0),
                mstatus: hardware_hart.csrs().mstatus.read_value().try_into().unwrap_or(0),
                // TODO: mstatusH exists only in rv32. Adjust this to support rv32
                mstatusH: 0,
            },
        }
    }

    pub fn regs(&mut self) -> &mut opensbi_sys::sbi_trap_regs {
        &mut self.regs
    }

    pub fn into_regs(self) -> opensbi_sys::sbi_trap_regs {
        self.regs
    }
}

#[derive(Debug)]
pub struct OpensbiResult {
    trap_regs: opensbi_sys::sbi_trap_regs,
}

impl OpensbiResult {
    pub fn from_opensbi_handler(trap_regs: opensbi_sys::sbi_trap_regs) -> Self {
        Self { trap_regs }
    }

    pub fn mstatus(&self) -> usize {
        self.trap_regs.mstatus.try_into().unwrap()
    }

    pub fn mepc(&self) -> usize {
        self.trap_regs.mepc.try_into().unwrap()
    }

    pub fn a0(&self) -> usize {
        self.trap_regs.a0.try_into().unwrap()
    }

    pub fn a1(&self) -> usize {
        self.trap_regs.a1.try_into().unwrap()
    }
}
