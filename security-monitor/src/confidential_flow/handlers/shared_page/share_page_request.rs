// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::{SbiRequest, SbiResponse};
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::riscv::sbi::CovgExtension;
use crate::core::architecture::{GeneralPurposeRegister, SharedPage};
use crate::core::control_data::{ConfidentialHart, ResumableOperation};
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::error::Error;
use crate::non_confidential_flow::DeclassifyToHypervisor;

/// Handles a request from the confidential VM about creating a shared page.
///
/// Control flows to the hypervisor when the sharing of the given `guest physical address` is allowed. The hypervisor is requested to
/// allocate a page of non-confidential memory and return back the `host physical address` of this page. Control flows back to the
/// confidential hart if the request was invalid, e.g., the `guest physical address` was not correct.
pub struct SharePageRequest {
    pub confidential_vm_physical_address: usize,
    pub size: usize,
}

impl SharePageRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self {
            confidential_vm_physical_address: confidential_hart.gprs().read(GeneralPurposeRegister::a0),
            size: confidential_hart.gprs().read(GeneralPurposeRegister::a1),
        }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        match self.share_page_sbi_request() {
            Ok(sbi_request) => confidential_flow
                .set_resumable_operation(ResumableOperation::SharePage(self))
                .into_non_confidential_flow()
                .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::SbiRequest(sbi_request)),
            Err(error) => {
                confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(SbiResponse::error(error)))
            }
        }
    }

    fn share_page_sbi_request(&self) -> Result<SbiRequest, Error> {
        let address = ConfidentialVmPhysicalAddress::new(self.confidential_vm_physical_address)?;
        ensure!(address.usize() % SharedPage::SIZE.in_bytes() == 0, Error::AddressNotAligned())?;
        ensure!(self.size == SharedPage::SIZE.in_bytes(), Error::InvalidParameter())?;
        Ok(SbiRequest::new(CovgExtension::EXTID, CovgExtension::SBI_EXT_COVG_SHARE_MEMORY, address.usize(), self.size))
    }
}
