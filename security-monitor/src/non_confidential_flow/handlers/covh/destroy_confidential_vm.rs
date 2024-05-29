// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialVmId, ControlData, HypervisorHart};
use crate::non_confidential_flow::handlers::sbi::SbiResponse;
use crate::non_confidential_flow::{ApplyToHypervisorHart, NonConfidentialFlow};

/// Handles the hypervisor request to destory the confidential VM's execution.
pub struct DestroyConfidentialVm {
    confidential_vm_id: ConfidentialVmId,
}

impl DestroyConfidentialVm {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self { confidential_vm_id: ConfidentialVmId::new(hypervisor_hart.gprs().read(GeneralPurposeRegister::a0)) }
    }

    pub fn handle(self, non_confidential_flow: NonConfidentialFlow) -> ! {
        non_confidential_flow.apply_and_exit_to_hypervisor(ApplyToHypervisorHart::SbiResponse(
            ControlData::remove_confidential_vm(self.confidential_vm_id)
                .map_or_else(|error| SbiResponse::error(error), |_| SbiResponse::success()),
        ))
    }
}
