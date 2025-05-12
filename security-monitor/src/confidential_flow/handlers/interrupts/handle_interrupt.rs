// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::specification::{MIE_MSIP_MASK, SCAUSE_INTERRUPT_MASK};
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
        use crate::core::architecture::specification::MIE_SSIP_MASK;
        if self.pending_interrupts & MIE_SSIP_MASK > 0 {
            crate::core::architecture::CSR.mip.read_and_clear_bits(MIE_SSIP_MASK);
            confidential_flow.resume_confidential_hart_execution();
        } else {
            confidential_flow.into_non_confidential_flow().declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::Interrupt(self))
        }
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        let scause = hypervisor_hart.csrs().scause.read_from_main_memory();
        hypervisor_hart.csrs_mut().scause.write(scause | self.pending_interrupts | SCAUSE_INTERRUPT_MASK);
        SbiResponse::success().declassify_to_hypervisor_hart(hypervisor_hart);
    }
}
