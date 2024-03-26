// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResult;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::{HartLifecycleState, MIE_MTIP_MASK, MIE_SSIP_MASK, MIE_STIP_MASK, SCAUSE_INTERRUPT_MASK};
use crate::core::control_data::{ConfidentialHart, HypervisorHart};
use crate::core::transformations::{DeclassifyToHypervisor, ExposeToHypervisor};

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
    /// - to the confidential hart in case of software interrupts
    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        if self.pending_interrupts & MIE_SSIP_MASK > 0 {
            // One of the reasons why the confidential hart was interrupted with SSIP is that it got an `InterHartRequest` from
            // another confidential hart. If this is the case, we must process all queued requests before resuming confidential
            // hart's execution.
            //
            // This piece of code executes because a confidential hart was interrupted with supervisor software interrupt to
            // process IPIs.
            confidential_flow.process_inter_hart_requests();
            // It might have happened, that this confidential hart has been shutdown when processing an IPI. I.e., there was
            // an IPI from other confidential hart that requested this confidential hart to shutdown. If this happened, we
            // cannot resume this confidential hart anymore. We must exit to the hypervisor and inform it about it.
            if confidential_flow.confidential_hart().lifecycle_state() == &HartLifecycleState::Shutdown {
                crate::confidential_flow::handlers::shutdown::shutdown_confidential_hart(confidential_flow);
            }
        }

        // the only interrupts that we can see here are:
        // * M-mode timer that the security monitor set to preemt execution of a confidential VM
        // * M-mode software or external interrupt
        let declassifier = if self.pending_interrupts & (MIE_MTIP_MASK | MIE_STIP_MASK) > 0 {
            // inject timer interrupt to the hypervisor
            DeclassifyToHypervisor::InterruptRequest(self)
        } else {
            // resume the hypervisor, it will trap again in the security monitor to process these interrupts
            DeclassifyToHypervisor::SbiResult(SbiResult::success(0))
        };
        confidential_flow.into_non_confidential_flow(declassifier).exit_to_hypervisor(ExposeToHypervisor::Resume())
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.csrs_mut().scause.set(self.pending_interrupts | SCAUSE_INTERRUPT_MASK);
        hypervisor_hart.apply_trap(false);
    }
}
