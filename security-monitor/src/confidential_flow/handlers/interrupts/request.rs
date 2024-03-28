// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::{ConfidentialFlow, DeclassifyToHypervisor};
use crate::core::architecture::{MIE_SSIP_MASK, SCAUSE_INTERRUPT_MASK};
use crate::core::control_data::{ConfidentialHart, HypervisorHart};

pub struct InterruptRequest {
    pending_interrupts: usize,
}

impl InterruptRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { pending_interrupts: confidential_hart.csrs().mip.read() }
    }

    /// Handles interrupts of a confidential hart.
    ///
    /// The control flows:
    /// - to the hypervisor when an interrupt comes from a hardware device.
    /// - to the confidential hart in case of IPIS
    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        if self.pending_interrupts & MIE_SSIP_MASK > 0 {
            // One of the reasons why the confidential hart was interrupted with SSIP is that it got an `InterHartRequest` from
            // another confidential hart. If this is the case, we must process all queued requests before resuming confidential
            // hart's execution. This is done as part of the procedure that resumes confidential hart execution.
            confidential_flow.resume_confidential_hart_execution();
        } else {
            // The only interrupts that we can see here are:
            // * M-mode timer that the security monitor set to preemt execution of a confidential VM
            // * M-mode software or external interrupt
            confidential_flow.into_non_confidential_flow().declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::InterruptRequest(self))
        }
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.csrs_mut().scause.set(self.pending_interrupts | SCAUSE_INTERRUPT_MASK);
        hypervisor_hart.apply_trap(false);
    }
}
