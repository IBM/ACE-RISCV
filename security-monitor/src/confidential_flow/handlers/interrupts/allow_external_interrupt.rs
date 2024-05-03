// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiRequest;
use crate::confidential_flow::{ConfidentialFlow, DeclassifyToHypervisor};
use crate::core::architecture::{CovgExtension, GeneralPurposeRegister};
use crate::core::control_data::{ConfidentialHart, PendingRequest};

pub struct AllowExternalInterrupt {
    interrupt_id: usize,
}

impl AllowExternalInterrupt {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { interrupt_id: confidential_hart.gprs().read(GeneralPurposeRegister::a0) }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        if self.interrupt_id == usize::MAX {
            // allow all interrupts
            debug!("Allow all interrupts");
        } else {
            // allow
            debug!("ALLOW EXT INTER {:x}", self.interrupt_id);
        }
        let sbi_request = SbiRequest::new(CovgExtension::EXTID, CovgExtension::SBI_EXT_COVG_ALLOW_EXT_INTERRUPT, 0, 0, 0, 0, 0, 0);
        confidential_flow
            .set_pending_request(PendingRequest::SbiRequest())
            .into_non_confidential_flow()
            .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::SbiRequest(sbi_request))
    }
}
