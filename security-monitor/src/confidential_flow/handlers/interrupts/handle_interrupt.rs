// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::{MIE_SSIP_MASK, SCAUSE_INTERRUPT_MASK};
use crate::core::control_data::{ConfidentialHart, HypervisorHart};
use crate::non_confidential_flow::DeclassifyToHypervisor;

/// Handles an interrupt that occured during the execution of a confidential hart. The control flows (a) to the hypervisor when an interrupt
/// comes from a hardware device, or (b) to the confidential hart in case of an IPI from other confidential hart.
pub struct HandleInterrupt {
    pending_interrupts: usize,
}

impl HandleInterrupt {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { pending_interrupts: confidential_hart.csrs().mip.read() }
    }

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
            confidential_flow.into_non_confidential_flow().declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::Interrupt(self))
        }
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.csrs_mut().scause.set(self.pending_interrupts | SCAUSE_INTERRUPT_MASK);
        SbiResponse::success(0).declassify_to_hypervisor_hart(hypervisor_hart);
    }
}
