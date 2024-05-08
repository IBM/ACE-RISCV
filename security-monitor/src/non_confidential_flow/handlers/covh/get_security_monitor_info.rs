// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::supervisor_binary_interface::cove::{SecurityMonitorInfo, SecurityMonitorState};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::HypervisorHart;
use crate::core::memory_layout::NonConfidentialMemoryAddress;
use crate::error::Error;
use crate::non_confidential_flow::handlers::sbi::SbiResponse;
use crate::non_confidential_flow::{ApplyToHypervisorHart, NonConfidentialFlow};

/// Returns information to the hypervisor about the state of the security monitor.
/// This handler implements the COVE Host Get TSM Info function from the COVH ABI.
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
        non_confidential_flow.apply_and_exit_to_hypervisor(ApplyToHypervisorHart::SbiResponse(
            self.fill_tsm_info_state()
                .map_or_else(|error| SbiResponse::error(error), |number_of_bytes_written| SbiResponse::success(number_of_bytes_written)),
        ))
    }

    fn fill_tsm_info_state(&self) -> Result<usize, Error> {
        let ptr = NonConfidentialMemoryAddress::new(self.tsm_info_address as *mut usize)?;
        NonConfidentialMemoryAddress::new((self.tsm_info_address + self.tsm_info_len) as *mut usize)?;
        ensure!(self.tsm_info_len >= core::mem::size_of::<SecurityMonitorInfo>(), Error::InvalidArgument())?;
        let info = SecurityMonitorInfo {
            security_monitor_state: SecurityMonitorState::Ready,
            security_monitor_version: self.get_version(),
            state_pages: 0,
            max_vcpus: 32,
            vcpu_state_pages: 0,
        };
        unsafe { (ptr.as_ptr() as *mut SecurityMonitorInfo).write(info) };
        Ok(core::mem::size_of::<SecurityMonitorInfo>())
    }

    fn get_version(&self) -> u32 {
        let major_version = env!("CARGO_PKG_VERSION_MAJOR").parse::<u32>().unwrap_or(0);
        let minor_version = env!("CARGO_PKG_VERSION_MINOR").parse::<u32>().unwrap_or(0);
        (major_version << 16) | minor_version
    }
}
