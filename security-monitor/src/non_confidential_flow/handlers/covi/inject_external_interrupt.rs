// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{
    ConfidentialHart, ConfidentialHartRemoteCommand, ConfidentialHartRemoteCommandExecutable, ConfidentialVmId, ControlData, HypervisorHart,
};
use crate::non_confidential_flow::handlers::sbi::SbiResponse;
use crate::non_confidential_flow::{ApplyToHypervisorHart, NonConfidentialFlow};

/// Injects external interrupt given by the hypervisor to the confidential hart. This handler implements the function COVE Interrupt Inject
/// TVM CPU from the CoVE's COVI ABI.
///
/// Only external interrupts allowed by the confidential VM are injected.
#[derive(Clone)]
pub struct InjectExternalInterrupt {
    confidential_vm_id: ConfidentialVmId,
    confidential_hart_id: usize,
    interrupt_id: usize,
}

impl InjectExternalInterrupt {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self {
            confidential_vm_id: ConfidentialVmId::new(hypervisor_hart.gprs().read(GeneralPurposeRegister::a0)),
            confidential_hart_id: hypervisor_hart.gprs().read(GeneralPurposeRegister::a1),
            interrupt_id: hypervisor_hart.gprs().read(GeneralPurposeRegister::a2),
        }
    }

    pub fn handle(mut self, mut non_confidential_flow: NonConfidentialFlow) -> ! {
        let transformation = ControlData::try_confidential_vm_mut(self.confidential_vm_id, |mut confidential_vm| {
            self.interrupt_id = self.interrupt_id & confidential_vm.allowed_external_interrupts();
            non_confidential_flow.swap_mscratch();
            let command = ConfidentialHartRemoteCommand::ExternalInterrupt(self);
            let result = confidential_vm.broadcast_remote_command(command);
            // We must revert the content of mscratch back to the value expected by our context switched.
            non_confidential_flow.swap_mscratch();
            result
        })
        .and_then(|_| Ok(SbiResponse::success()))
        .unwrap_or_else(|error| SbiResponse::error(error));
        non_confidential_flow.apply_and_exit_to_hypervisor(ApplyToHypervisorHart::SbiResponse(transformation))
    }
}

impl ConfidentialHartRemoteCommandExecutable for InjectExternalInterrupt {
    fn execute_on_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        confidential_hart.csrs_mut().hvip.save_value(self.interrupt_id);
    }

    fn is_hart_selected(&self, hart_id: usize) -> bool {
        self.confidential_hart_id == hart_id
    }
}
