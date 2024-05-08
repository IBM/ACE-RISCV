// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::DeclassifyToConfidentialVm;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialVmId, HypervisorHart};
use crate::non_confidential_flow::handlers::covi::InjectExternalInterrupt;
use crate::non_confidential_flow::handlers::sbi::SbiResponse;
use crate::non_confidential_flow::{ApplyToHypervisorHart, NonConfidentialFlow};

/// Handles the hypervisor request to resume execution of a confidential hart.
pub struct RunConfidentialHart {
    confidential_vm_id: ConfidentialVmId,
    confidential_hart_id: usize,
    inject_external_interrupt: InjectExternalInterrupt,
}

impl RunConfidentialHart {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self {
            confidential_vm_id: ConfidentialVmId::new(hypervisor_hart.gprs().read(GeneralPurposeRegister::a0)),
            confidential_hart_id: hypervisor_hart.gprs().read(GeneralPurposeRegister::a1),
            inject_external_interrupt: InjectExternalInterrupt::from_hypervisor_hart(hypervisor_hart),
        }
    }

    pub fn handle(self, non_confidential_flow: NonConfidentialFlow) -> ! {
        match non_confidential_flow.into_confidential_flow(self.confidential_vm_id, self.confidential_hart_id) {
            Ok(confidential_flow) => confidential_flow
                .declassify_to_confidential_hart(DeclassifyToConfidentialVm::ExternalInterrupt(self.inject_external_interrupt))
                .resume_confidential_hart_execution(),
            Err((non_confidential_flow, error)) => {
                // Properly implemented hypervisor should never let us enter this code. Entering this code means that the
                // transition into confidential flow failed. This might indicate an error in the hypervisor implementation
                // because the hypervisor tried to schedule an invalid confidential VM, an invalid confidential hart, or a
                // confidential hart that is already running on another physical hart.
                let transformation = ApplyToHypervisorHart::SbiResponse(SbiResponse::error(error));
                non_confidential_flow.apply_and_exit_to_hypervisor(transformation)
            }
        }
    }
}
