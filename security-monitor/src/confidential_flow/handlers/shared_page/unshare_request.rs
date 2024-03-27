// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResult;
use crate::confidential_flow::{ApplyToConfidentialVm, ConfidentialFlow};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, ControlData};
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;

#[derive(PartialEq)]
pub struct UnsharePageRequest {
    address: ConfidentialVmPhysicalAddress,
}

impl UnsharePageRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let address = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        Self { address: ConfidentialVmPhysicalAddress::new(address) }
    }

    /// Handles a request from the confidential VM to unshare a page that was previously shared with the hypervisor.
    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let transformation = ControlData::try_confidential_vm_mut(confidential_flow.confidential_vm_id(), |mut confidential_vm| {
            confidential_vm.unmap_shared_page(self.address())
        })
        .and_then(|_| Ok(ApplyToConfidentialVm::SbiResult(SbiResult::success(0))))
        .unwrap_or_else(|error| error.into_confidential_transformation());
        confidential_flow.exit_to_confidential_hart(transformation)
    }

    pub fn address(&self) -> &ConfidentialVmPhysicalAddress {
        &self.address
    }
}
