// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiRequest;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::supervisor_binary_interface::CovgExtension;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, PendingRequest};
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::non_confidential_flow::DeclassifyToHypervisor;

/// Handles a request from the confidential VM about creating a shared page.
///
/// Control flows to the hypervisor when the sharing of the given `guest physical address` is allowed. The hypervisor is requested to
/// allocate a page of non-confidential memory and return back the `host physical address` of this page. Control flows back to the
/// confidential hart if the request was invalid, e.g., the `guest physical address` was not correct.
pub struct SharePageRequest {
    pub address: ConfidentialVmPhysicalAddress,
    pub size: usize,
}

impl SharePageRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let address = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        let size = confidential_hart.gprs().read(GeneralPurposeRegister::a1);
        // TODO: make sure address is aligned to the page size
        Self { address: ConfidentialVmPhysicalAddress::new(address), size }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let sbi_request = self.share_page_sbi_request();
        confidential_flow
            .set_pending_request(PendingRequest::SharePage(self))
            .into_non_confidential_flow()
            .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::SbiRequest(sbi_request))
    }

    fn share_page_sbi_request(&self) -> SbiRequest {
        SbiRequest::new(CovgExtension::EXTID, CovgExtension::SBI_EXT_COVG_SHARE_MEMORY, self.address.usize(), self.size)
    }
}
