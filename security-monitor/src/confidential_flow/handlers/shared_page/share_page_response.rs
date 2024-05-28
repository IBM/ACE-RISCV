// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::handlers::shared_page::SharePageRequest;
use crate::confidential_flow::handlers::symmetrical_multiprocessing::SbiRemoteHfenceGvmaVmid;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHartRemoteCommand, ControlData, HypervisorHart};
use crate::core::memory_layout::NonConfidentialMemoryAddress;
use crate::core::memory_protector::SharedPage;

/// Finishes the pending request of sharing a page between the confidential VM and the hypervisor. The hypervisor should provide information
/// about the shared page located in non-confidential memory. The security monitor will map this page into the address space of the
/// confidential VM.
///
/// Control flows always to the confidential VM.
pub struct SharePageResponse {
    response_code: usize,
    hypervisor_page_address: usize,
    request: SharePageRequest,
}

impl SharePageResponse {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart, request: SharePageRequest) -> Self {
        Self {
            response_code: hypervisor_hart.shared_memory().gpr(GeneralPurposeRegister::a0),
            hypervisor_page_address: hypervisor_hart.shared_memory().gpr(GeneralPurposeRegister::a1),
            request,
        }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        if self.response_code > 0 {
            // Hypervisor returned an error informing that it could not allocate shared pages. Expose this information the
            // confidential VM.
            let transformation = ApplyToConfidentialHart::SbiResponse(SbiResponse::failure(self.response_code));
            confidential_flow.apply_and_exit_to_confidential_hart(transformation);
        }

        // Security: check that the start address is located in the non-confidential memory
        let transformation = match NonConfidentialMemoryAddress::new(self.hypervisor_page_address as *mut usize) {
            Ok(hypervisor_address) => {
                ControlData::try_confidential_vm_mut(confidential_flow.confidential_vm_id(), |mut confidential_vm| {
                    confidential_vm.memory_protector_mut().map_shared_page(hypervisor_address, self.request.address)?;
                    let request =
                        SbiRemoteHfenceGvmaVmid::all_harts(&self.request.address, SharedPage::SIZE, confidential_flow.confidential_vm_id());
                    confidential_vm.broadcast_remote_command(ConfidentialHartRemoteCommand::SbiRemoteHfenceGvmaVmid(request))?;
                    Ok(())
                })
                .and_then(|_| Ok(SbiResponse::success(0)))
                .unwrap_or_else(|error| SbiResponse::failure(error.code()))
            }
            Err(error) => SbiResponse::failure(error.code()),
        };
        confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(transformation))
    }
}
