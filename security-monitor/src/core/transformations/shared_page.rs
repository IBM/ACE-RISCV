// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::ConfidentialHart;
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::core::memory_protector::PageSize;
use crate::error::Error;

#[derive(PartialEq)]
pub struct SharePageRequest {
    address: ConfidentialVmPhysicalAddress,
    page_size: PageSize,
}

impl SharePageRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let address = confidential_hart.gpr(GeneralPurposeRegister::a0);
        Self { address: ConfidentialVmPhysicalAddress::new(address), page_size: PageSize::Size4KiB }
    }

    pub fn confidential_vm_physical_address(&self) -> &ConfidentialVmPhysicalAddress {
        &self.address
    }

    pub fn page_size(&self) -> PageSize {
        self.page_size
    }
}

#[derive(PartialEq)]
pub struct SharePageResult {
    response_code: usize,
    hypervisor_page_address: usize,
}

impl SharePageResult {
    pub fn new(response_code: usize, hypervisor_page_address: usize) -> Self {
        Self { response_code, hypervisor_page_address }
    }

    pub fn is_error(&self) -> bool {
        self.response_code > 0
    }

    pub fn response_code(&self) -> usize {
        self.response_code
    }

    pub fn hypervisor_page_address(&self) -> usize {
        self.hypervisor_page_address
    }
}

#[derive(PartialEq)]
pub struct UnsharePageRequest {
    address: ConfidentialVmPhysicalAddress,
}

impl UnsharePageRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let address = confidential_hart.gpr(GeneralPurposeRegister::a0);
        Self { address: ConfidentialVmPhysicalAddress::new(address) }
    }

    pub fn address(&self) -> &ConfidentialVmPhysicalAddress {
        &self.address
    }
}
