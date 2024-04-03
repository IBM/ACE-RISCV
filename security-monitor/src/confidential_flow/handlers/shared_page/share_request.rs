// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiRequest;
use crate::confidential_flow::{ConfidentialFlow, DeclassifyToHypervisor};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, PendingRequest};
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::core::memory_protector::PageSize;

/// Handles a request from the confidential VM about creating a shared page.
///
/// Control flows to the hypervisor when the sharing of the given `guest physical address` is allowed. The hypervisor is requested to
/// allocate a page of non-confidential memory and return back the `host physical address` of this page. Control flows back to the
/// confidential hart if the request was invalid, e.g., the `guest physical address` was not correct.
pub struct SharePageRequest {
    address: ConfidentialVmPhysicalAddress,
    page_size: PageSize,
}

impl SharePageRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let address = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        Self { address: ConfidentialVmPhysicalAddress::new(address), page_size: PageSize::Size4KiB }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let sbi_request = SbiRequest::kvm_ace_page_in(self.address.usize());
        confidential_flow
            .set_pending_request(PendingRequest::SharePage(self))
            .into_non_confidential_flow()
            .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::SbiRequest(sbi_request))
    }

    pub fn confidential_vm_physical_address(&self) -> &ConfidentialVmPhysicalAddress {
        &self.address
    }

    pub fn page_size(&self) -> PageSize {
        self.page_size
    }
}
