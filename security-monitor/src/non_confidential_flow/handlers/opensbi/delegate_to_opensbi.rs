// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::HypervisorHart;
use crate::non_confidential_flow::{ApplyToHypervisorHart, NonConfidentialFlow};
use opensbi_sys::sbi_trap_regs;

extern "C" {
    fn sbi_trap_handler(regs: *mut sbi_trap_regs) -> *mut sbi_trap_regs;
}

/// Handles call from the hypervisor to OpenSBI firmware by delegating it to the OpenSBI trap handler.
pub struct DelegateToOpensbi {
    trap_regs: opensbi_sys::sbi_trap_regs,
}

impl DelegateToOpensbi {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self {
            trap_regs: opensbi_sys::sbi_trap_regs {
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
                mepc: hypervisor_hart.csrs().mepc.read_from_main_memory().try_into().unwrap_or(0),
                mstatus: hypervisor_hart.csrs().mstatus.read_from_main_memory().try_into().unwrap_or(0),
                // TODO: mstatusH exists only in rv32. Adjust this in case we want to support rv32
                mstatusH: 0,
            },
        }
    }

    pub fn handle(mut self, mut non_confidential_flow: NonConfidentialFlow) -> ! {
        // We must ensure that the swap is called twice, before and after executing the OpenSBI handler. Otherwise, we end
        // up having incorrect address in mscratch and the context switches to/from the security monitor will not work
        // anymore.
        non_confidential_flow.swap_mscratch();
        unsafe { sbi_trap_handler(&mut self.trap_regs as *mut _) };
        non_confidential_flow.swap_mscratch();

        non_confidential_flow.apply_and_exit_to_hypervisor(ApplyToHypervisorHart::OpenSbiResponse(self))
    }

    pub fn apply_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a0, self.trap_regs.a0.try_into().unwrap());
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a1, self.trap_regs.a1.try_into().unwrap());
        hypervisor_hart.csrs_mut().mstatus.save_value_in_main_memory(self.trap_regs.mstatus.try_into().unwrap());
        hypervisor_hart.csrs_mut().mepc.save_value_in_main_memory(self.trap_regs.mepc.try_into().unwrap());
    }
}
