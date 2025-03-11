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
pub struct DelegateInterruptToOpensbi {}

impl DelegateInterruptToOpensbi {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self {}
    }

    pub fn handle(mut self, mut non_confidential_flow: NonConfidentialFlow) -> ! {
        // We must ensure that the swap is called twice, before and after executing the OpenSBI handler. Otherwise, we end
        // up having incorrect address in mscratch and the context switches to/from the security monitor will not work
        // anymore.
        non_confidential_flow.swap_mscratch();
        unsafe { sbi_trap_handler(core::ptr::null_mut()) };
        non_confidential_flow.swap_mscratch();

        non_confidential_flow.resume_hypervisor_hart_execution()
    }
}
