// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::HypervisorHart;
use crate::non_confidential_flow::{ApplyToHypervisor, NonConfidentialFlow};
use opensbi_sys::sbi_trap_regs;

extern "C" {
    fn sbi_trap_handler(regs: *mut sbi_trap_regs) -> *mut sbi_trap_regs;
}

#[derive(Debug)]
pub struct OpensbiRequest {
    regs: opensbi_sys::sbi_trap_regs,
}

impl OpensbiRequest {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self {
            regs: opensbi_sys::sbi_trap_regs {
                zero: 0,
                ra: hypervisor_hart.gprs().read(GeneralPurposeRegister::ra).try_into().unwrap_or(0),
                sp: hypervisor_hart.gprs().read(GeneralPurposeRegister::sp).try_into().unwrap_or(0),
                gp: hypervisor_hart.gprs().read(GeneralPurposeRegister::gp).try_into().unwrap_or(0),
                tp: hypervisor_hart.gprs().read(GeneralPurposeRegister::tp).try_into().unwrap_or(0),
                t0: hypervisor_hart.gprs().read(GeneralPurposeRegister::t0).try_into().unwrap_or(0),
                t1: hypervisor_hart.gprs().read(GeneralPurposeRegister::t1).try_into().unwrap_or(0),
                t2: hypervisor_hart.gprs().read(GeneralPurposeRegister::t2).try_into().unwrap_or(0),
                s0: hypervisor_hart.gprs().read(GeneralPurposeRegister::s0).try_into().unwrap_or(0),
                s1: hypervisor_hart.gprs().read(GeneralPurposeRegister::s1).try_into().unwrap_or(0),
                a0: hypervisor_hart.gprs().read(GeneralPurposeRegister::a0).try_into().unwrap_or(0),
                a1: hypervisor_hart.gprs().read(GeneralPurposeRegister::a1).try_into().unwrap_or(0),
                a2: hypervisor_hart.gprs().read(GeneralPurposeRegister::a2).try_into().unwrap_or(0),
                a3: hypervisor_hart.gprs().read(GeneralPurposeRegister::a3).try_into().unwrap_or(0),
                a4: hypervisor_hart.gprs().read(GeneralPurposeRegister::a4).try_into().unwrap_or(0),
                a5: hypervisor_hart.gprs().read(GeneralPurposeRegister::a5).try_into().unwrap_or(0),
                a6: hypervisor_hart.gprs().read(GeneralPurposeRegister::a6).try_into().unwrap_or(0),
                a7: hypervisor_hart.gprs().read(GeneralPurposeRegister::a7).try_into().unwrap_or(0),
                s2: hypervisor_hart.gprs().read(GeneralPurposeRegister::s2).try_into().unwrap_or(0),
                s3: hypervisor_hart.gprs().read(GeneralPurposeRegister::s3).try_into().unwrap_or(0),
                s4: hypervisor_hart.gprs().read(GeneralPurposeRegister::s4).try_into().unwrap_or(0),
                s5: hypervisor_hart.gprs().read(GeneralPurposeRegister::s5).try_into().unwrap_or(0),
                s6: hypervisor_hart.gprs().read(GeneralPurposeRegister::s6).try_into().unwrap_or(0),
                s7: hypervisor_hart.gprs().read(GeneralPurposeRegister::s7).try_into().unwrap_or(0),
                s8: hypervisor_hart.gprs().read(GeneralPurposeRegister::s8).try_into().unwrap_or(0),
                s9: hypervisor_hart.gprs().read(GeneralPurposeRegister::s9).try_into().unwrap_or(0),
                s10: hypervisor_hart.gprs().read(GeneralPurposeRegister::s10).try_into().unwrap_or(0),
                s11: hypervisor_hart.gprs().read(GeneralPurposeRegister::s11).try_into().unwrap_or(0),
                t3: hypervisor_hart.gprs().read(GeneralPurposeRegister::t3).try_into().unwrap_or(0),
                t4: hypervisor_hart.gprs().read(GeneralPurposeRegister::t4).try_into().unwrap_or(0),
                t5: hypervisor_hart.gprs().read(GeneralPurposeRegister::t5).try_into().unwrap_or(0),
                t6: hypervisor_hart.gprs().read(GeneralPurposeRegister::t6).try_into().unwrap_or(0),
                mepc: hypervisor_hart.csrs().mepc.read_value().try_into().unwrap_or(0),
                mstatus: hypervisor_hart.csrs().mstatus.read_value().try_into().unwrap_or(0),
                // TODO: mstatusH exists only in rv32. Adjust this to support rv32
                mstatusH: 0,
            },
        }
    }

    /// OpenSBI handler processes regular SBI calls sent by a hypervisor or VMs
    pub fn handle(mut self, mut non_confidential_flow: NonConfidentialFlow) -> ! {
        // We must ensure that the swap is called twice, before and after executing the OpenSBI handler. Otherwise, we end
        // up having incorrect address in mscratch and the context switches to/from the security monitor will not work
        // anymore.
        non_confidential_flow.swap_mscratch();
        unsafe { sbi_trap_handler(&mut self.regs as *mut _) };
        non_confidential_flow.swap_mscratch();

        let transformation = ApplyToHypervisor::OpensbiResult(OpensbiResult::from_opensbi_handler(self.regs));
        non_confidential_flow.exit_to_hypervisor(transformation)
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

    pub fn apply_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        let a0 = self.trap_regs.a0.try_into().unwrap();
        let a1 = self.trap_regs.a1.try_into().unwrap();
        let mstatus = self.trap_regs.mstatus.try_into().unwrap();
        let mepc = self.trap_regs.mepc.try_into().unwrap();

        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a0, a0);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a1, a1);
        hypervisor_hart.csrs_mut().mstatus.save_value(mstatus);
        hypervisor_hart.csrs_mut().mepc.save_value(mepc);
    }
}
