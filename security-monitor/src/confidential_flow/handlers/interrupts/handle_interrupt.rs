// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::specification::{MIE_MSIP_MASK, MIE_SSIP_MASK, SCAUSE_INTERRUPT_MASK};
use crate::core::architecture::CSR;
use crate::core::control_data::{ConfidentialHart, HypervisorHart};
use crate::non_confidential_flow::DeclassifyToHypervisor;

/// Handles an interrupt that occured during the execution of a confidential hart. The control flows (a) to the hypervisor when an interrupt
/// comes from a hardware device, or (b) to the confidential hart in case of an IPI from other confidential hart.
pub struct HandleInterrupt();

impl HandleInterrupt {
    pub fn from_confidential_hart(_confidential_hart: &ConfidentialHart) -> Self {
        Self {}
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        if CSR.mip.read() & MIE_MSIP_MASK > 0 {
            if confidential_flow.process_confidential_hart_remote_commands() {
                CSR.mip.read_and_clear_bits(MIE_SSIP_MASK);
                confidential_flow.resume_confidential_hart_execution();
            }
        }

        confidential_flow.into_non_confidential_flow().declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::Interrupt(self))
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.csrs_mut().scause.read_and_set_bits(SCAUSE_INTERRUPT_MASK);
        SbiResponse::success().declassify_to_hypervisor_hart(hypervisor_hart);
    }
}
