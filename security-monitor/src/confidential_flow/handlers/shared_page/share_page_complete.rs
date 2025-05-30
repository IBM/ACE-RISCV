// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::handlers::shared_page::SharePageRequest;
use crate::confidential_flow::handlers::symmetrical_multiprocessing::RemoteHfenceGvmaVmid;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::{GeneralPurposeRegister, PageSize};
use crate::core::control_data::{ConfidentialHartRemoteCommand, ControlDataStorage, HypervisorHart};
use crate::core::memory_layout::{ConfidentialVmPhysicalAddress, NonConfidentialMemoryAddress};
use crate::error::Error;

/// Finishes the pending request of sharing a page between the confidential VM and the hypervisor. The hypervisor should provide information
/// about the shared page located in non-confidential memory. The security monitor will map this page into the address space of the
/// confidential VM.
///
/// Control flows always to the confidential VM.
pub struct SharePageComplete {
    response_code: usize,
    hypervisor_page_address: usize,
    request: SharePageRequest,
}

impl SharePageComplete {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart, request: SharePageRequest) -> Self {
        Self {
            response_code: hypervisor_hart.shared_memory().gpr(GeneralPurposeRegister::a0),
            hypervisor_page_address: hypervisor_hart.shared_memory().gpr(GeneralPurposeRegister::a1),
            request,
        }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        let transformation = self
            .map_shared_page(&mut confidential_flow)
            .and_then(|_| Ok(SbiResponse::success()))
            .unwrap_or_else(|error| SbiResponse::error(error));
        confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(transformation))
    }

    fn map_shared_page(&self, confidential_flow: &mut ConfidentialFlow) -> Result<(), Error> {
        ensure!(self.response_code == 0, Error::Failed())?;
        // Security: check that the start address is located in the non-confidential memory and is properly aligned
        let hypervisor_address = NonConfidentialMemoryAddress::new(self.hypervisor_page_address as *mut usize)?;
        ensure!(hypervisor_address.usize() % PageSize::Size4KiB.in_bytes() == 0, Error::AddressNotAligned())?;
        let address = ConfidentialVmPhysicalAddress::new(self.request.confidential_vm_physical_address)?;
        ControlDataStorage::try_confidential_vm(confidential_flow.confidential_vm_id(), |confidential_vm| {
            let page_size = confidential_vm.memory_protector_mut().map_shared_page(hypervisor_address, &address)?;
            let request = RemoteHfenceGvmaVmid::all_harts(None, page_size, confidential_flow.confidential_vm_id());
            confidential_flow.broadcast_remote_command(&confidential_vm, ConfidentialHartRemoteCommand::RemoteHfenceGvmaVmid(request))?;
            Ok(())
        })
    }
}
