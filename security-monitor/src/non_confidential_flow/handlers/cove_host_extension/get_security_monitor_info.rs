// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::sbi::TsmInfo;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialVm, HypervisorHart};
use crate::core::memory_layout::NonConfidentialMemoryAddress;
use crate::error::Error;
use crate::non_confidential_flow::handlers::supervisor_binary_interface::SbiResponse;
use crate::non_confidential_flow::{ApplyToHypervisorHart, NonConfidentialFlow};

/// This handler implements the `Get TSM Info` function of the CoVE Host ABI.
///
/// Returns information to the hypervisor about the state and configuration of the security monitor.
///
/// Returns error to the caller if the given address range is not in the non-confidential memory or is not large enough to contain the
/// expected response.
pub struct GetSecurityMonitorInfo {
    tsm_info_address: usize,
    tsm_info_len: usize,
}

impl GetSecurityMonitorInfo {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self {
            tsm_info_address: hypervisor_hart.gprs().read(GeneralPurposeRegister::a0),
            tsm_info_len: hypervisor_hart.gprs().read(GeneralPurposeRegister::a1),
        }
    }

    pub fn handle(self, non_confidential_flow: NonConfidentialFlow) -> ! {
        let sbi_response = self.fill_tsm_info_state().map_or_else(
            |error| SbiResponse::error(error),
            |number_of_written_bytes| SbiResponse::success_with_code(number_of_written_bytes),
        );
        non_confidential_flow.apply_and_exit_to_hypervisor(ApplyToHypervisorHart::SbiResponse(sbi_response))
    }

    fn fill_tsm_info_state(&self) -> Result<usize, Error> {
        let info = TsmInfo {
            tsm_state: TsmInfo::COVE_TSM_STATE_READY,
            tsm_impl_id: TsmInfo::COVE_TSM_IMPL_ACE,
            tsm_version: self.get_version(),
            tsm_capabilities: TsmInfo::COVE_TSM_CAP_PROMOTE_TVM | TsmInfo::COVE_TSM_CAP_ATTESTATION_LOCAL_MASK,
            state_pages: 0,
            max_vcpus: u64::try_from(ConfidentialVm::MAX_NUMBER_OF_HARTS_PER_VM).unwrap_or(0),
            vcpu_state_pages: 0,
        };
        // Check that the input arguments define a memory region in non-confidential memory that is large enough to store the
        // `TsmInfo` structure.
        let ptr = NonConfidentialMemoryAddress::new(self.tsm_info_address as *mut usize)?;
        NonConfidentialMemoryAddress::new((self.tsm_info_address + self.tsm_info_len) as *mut usize)?;
        ensure!(self.tsm_info_len >= core::mem::size_of::<TsmInfo>(), Error::InvalidParameter())?;
        // below unsafe operation is ok because pointer is a valid address in non-confidential memory, and we have enough space to write the
        // reponse.
        unsafe { (ptr.as_ptr() as *mut TsmInfo).write(info) };
        Ok(core::mem::size_of::<TsmInfo>())
    }

    fn get_version(&self) -> u32 {
        let major_version = env!("CARGO_PKG_VERSION_MAJOR").parse::<u32>().unwrap_or(0);
        let minor_version = env!("CARGO_PKG_VERSION_MINOR").parse::<u32>().unwrap_or(0);
        (major_version << 16) | minor_version
    }
}
