// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiRequest;
use crate::confidential_flow::{ConfidentialFlow, DeclassifyToHypervisor};
use crate::core::architecture::{CovgExtension, GeneralPurposeRegister};
use crate::core::control_data::{ConfidentialHart, ControlData, PendingRequest};
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;

/// Handles a request from the confidential VM to unshare a page that was previously shared with the hypervisor.
pub struct UnsharePageRequest {
    address: ConfidentialVmPhysicalAddress,
    size: usize,
}

impl UnsharePageRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let address = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        let size = confidential_hart.gprs().read(GeneralPurposeRegister::a1);
        Self { address: ConfidentialVmPhysicalAddress::new(address), size }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        match ControlData::try_confidential_vm_mut(confidential_flow.confidential_vm_id(), |mut confidential_vm| {
            confidential_vm.unmap_shared_page(self.address())
        }) {
            Ok(_) => confidential_flow
                .set_pending_request(PendingRequest::SbiRequest())
                .into_non_confidential_flow()
                .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::SbiRequest(self.unshare_page_sbi_request())),
            Err(error) => {
                let transformation = error.into_confidential_transformation();
                confidential_flow.apply_and_exit_to_confidential_hart(transformation)
            }
        }
    }

    fn unshare_page_sbi_request(&self) -> SbiRequest {
        SbiRequest::new(CovgExtension::EXTID, CovgExtension::SBI_EXT_COVG_UNSHARE_MEMORY, self.address.usize(), self.size, 0, 0, 0, 0)
    }

    pub fn address(&self) -> &ConfidentialVmPhysicalAddress {
        &self.address
    }
}
