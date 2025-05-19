// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::{SbiRequest, SbiResponse};
use crate::confidential_flow::handlers::symmetrical_multiprocessing::RemoteHfenceGvmaVmid;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::riscv::sbi::CovgExtension;
use crate::core::architecture::{GeneralPurposeRegister, SharedPage};
use crate::core::control_data::{ConfidentialHart, ConfidentialHartRemoteCommand, ControlDataStorage, ResumableOperation};
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::error::Error;
use crate::non_confidential_flow::DeclassifyToHypervisor;

/// Unshared memory that has been previously shared with the hypervisor.
pub struct UnsharePageRequest {
    confidential_vm_physical_address: usize,
    size: usize,
}

impl UnsharePageRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self {
            confidential_vm_physical_address: confidential_hart.gprs().read(GeneralPurposeRegister::a0),
            size: confidential_hart.gprs().read(GeneralPurposeRegister::a1),
        }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        match self.unmap_shared_page(&mut confidential_flow) {
            Ok(sbi_request) => confidential_flow
                .set_resumable_operation(ResumableOperation::SbiRequest())
                .into_non_confidential_flow()
                .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::SbiRequest(sbi_request)),
            Err(error) => {
                confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(SbiResponse::error(error)))
            }
        }
    }

    fn unmap_shared_page(&self, confidential_flow: &mut ConfidentialFlow) -> Result<SbiRequest, Error> {
        let address = ConfidentialVmPhysicalAddress::new(self.confidential_vm_physical_address)?;
        ensure!(address.usize() % SharedPage::SIZE.in_bytes() == 0, Error::AddressNotAligned())?;
        ensure!(self.size == SharedPage::SIZE.in_bytes(), Error::InvalidParameter())?;

        let confidential_vm_id = confidential_flow.confidential_vm_id();
        ControlDataStorage::try_confidential_vm(confidential_vm_id, |confidential_vm| {
            let unmapped_page_size = confidential_vm.memory_protector_mut().unmap_shared_page(&address)?;
            let request = RemoteHfenceGvmaVmid::all_harts(None, unmapped_page_size, confidential_vm_id);
            confidential_flow.broadcast_remote_command(&confidential_vm, ConfidentialHartRemoteCommand::RemoteHfenceGvmaVmid(request))?;
            Ok(SbiRequest::new(CovgExtension::EXTID, CovgExtension::SBI_EXT_COVG_UNSHARE_MEMORY, address.usize(), self.size))
        })
    }
}
