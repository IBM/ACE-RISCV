// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::specification::{MIE_SSIP_MASK, SCAUSE_INTERRUPT_MASK};
use crate::core::control_data::{ConfidentialHart, HypervisorHart};
use crate::core::timer_controller::TimerController;
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

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        use crate::core::architecture::specification::*;
        if self.pending_interrupts & MIE_MEIP_MASK > 0 {
            confidential_flow.into_non_confidential_flow().declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::Interrupt(self))
        } else if self.pending_interrupts & MIE_MSIP_MASK > 0 {
            // One of the reasons why the confidential hart was interrupted with SSIP is that it got an `ConfidentialHartRemoteCommand` from
            // another confidential hart. If this is the case, we must process all queued requests before resuming confidential hart's
            // execution. This is done as part of the procedure that resumes confidential hart execution.
            confidential_flow.into_non_confidential_flow().declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::Interrupt(self))
        } else {
            // The only interrupts that we can see here are:
            // * M-mode timer that the security monitor set to preemt execution of a confidential VM
            // * S-mode timer that the hypervisor set to preemt execution of a confidential VM
            // * M-mode external interrupt
            let mut controller = TimerController::new(&mut confidential_flow);
            if controller.vs_timer_interrupted() {
                controller.handle_vs_interrupt();
                controller.set_s_timer();
                // if !controller.s_timer_interrupted() {
                //     confidential_flow.resume_confidential_hart_execution();
                // }
            }
            confidential_flow.into_non_confidential_flow().declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::Interrupt(self))
        }
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.csrs_mut().scause.write(self.pending_interrupts | SCAUSE_INTERRUPT_MASK);
        hypervisor_hart.csrs_mut().sip.read_and_set_bits(self.pending_interrupts);
        SbiResponse::success().declassify_to_hypervisor_hart(hypervisor_hart);
    }
}
