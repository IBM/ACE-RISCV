// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::{SbiRequest, SbiResponse};
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::supervisor_binary_interface::CovgExtension;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, ControlData, PendingRequest};
use crate::non_confidential_flow::DeclassifyToHypervisor;

pub struct AllowExternalInterrupt {
    interrupt_id: usize,
}

impl AllowExternalInterrupt {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { interrupt_id: confidential_hart.gprs().read(GeneralPurposeRegister::a0) }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        match ControlData::try_confidential_vm(confidential_flow.confidential_vm_id(), |mut confidential_vm| {
            Ok(confidential_vm.set_allowed_external_interrupts(self.interrupt_id))
        }) {
            Ok(_) => {
                let sbi_request =
                    SbiRequest::new(CovgExtension::EXTID, CovgExtension::SBI_EXT_COVG_ALLOW_EXT_INTERRUPT, self.interrupt_id, 0);
                confidential_flow
                    .set_pending_request(PendingRequest::SbiRequest())
                    .into_non_confidential_flow()
                    .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::SbiRequest(sbi_request))
            }
            Err(error) => {
                confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(SbiResponse::error(error)))
            }
        }
    }
}
