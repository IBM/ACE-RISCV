// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResult;
use crate::confidential_flow::handlers::shared_page::SharePageRequest;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ControlData, HypervisorHart};
use crate::core::memory_layout::NonConfidentialMemoryAddress;
use crate::core::transformations::ExposeToConfidentialVm;

#[derive(PartialEq)]
pub struct SharePageResult {
    response_code: usize,
    hypervisor_page_address: usize,
}

impl SharePageResult {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        let response_code = hypervisor_hart.gprs().read(GeneralPurposeRegister::a0);
        let hypervisor_page_address = hypervisor_hart.gprs().read(GeneralPurposeRegister::a1);
        Self { response_code, hypervisor_page_address }
    }

    /// Handles a response from the hypervisor about the creation of a shared page.
    ///
    /// Control always flows to the confidential VM.
    pub fn handle(self, confidential_flow: ConfidentialFlow, request: SharePageRequest) -> ! {
        if self.is_error() {
            // Hypervisor returned an error informing that it could not allocate shared pages. Expose this information the
            // confidential VM.
            let transformation = ExposeToConfidentialVm::SbiResult(SbiResult::failure(self.response_code()));
            confidential_flow.exit_to_confidential_hart(transformation);
        }

        // Security: check that the start address is located in the non-confidential memory
        match NonConfidentialMemoryAddress::new(self.hypervisor_page_address() as *mut usize) {
            Ok(hypervisor_address) => {
                let transformation = ControlData::try_confidential_vm_mut(confidential_flow.confidential_vm_id(), |mut confidential_vm| {
                    confidential_vm.map_shared_page(hypervisor_address, request.page_size(), *request.confidential_vm_physical_address())
                })
                .and_then(|_| Ok(ExposeToConfidentialVm::SbiResult(SbiResult::success(0))))
                .unwrap_or_else(|error| error.into_confidential_transformation());
                confidential_flow.exit_to_confidential_hart(transformation)
            }
            Err(error) => confidential_flow.exit_to_confidential_hart(error.into_confidential_transformation()),
        }
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
