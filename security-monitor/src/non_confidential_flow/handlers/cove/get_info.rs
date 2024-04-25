// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::HypervisorHart;
use crate::core::memory_layout::NonConfidentialMemoryAddress;
use crate::error::Error;
use crate::non_confidential_flow::{ApplyToHypervisor, NonConfidentialFlow};

pub struct GetInfoHandler {
    tsm_info_address: usize,
    tsm_info_len: usize,
}

impl GetInfoHandler {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self {
            tsm_info_address: hypervisor_hart.gprs().read(GeneralPurposeRegister::a0),
            tsm_info_len: hypervisor_hart.gprs().read(GeneralPurposeRegister::a1),
        }
    }

    pub fn handle(self, mut non_confidential_flow: NonConfidentialFlow) -> ! {
        debug!("Handle get info");
        let sbi_response = match self.fill_tsm_info_state() {
            Ok(number_of_bytes_written) => ApplyToHypervisor::SbiResponse(SbiResponse::success(number_of_bytes_written)),
            Err(error) => error.into_non_confidential_transformation(),
        };
        non_confidential_flow.apply_and_exit_to_hypervisor(sbi_response)
    }

    fn fill_tsm_info_state(&self) -> Result<usize, Error> {
        let mut ptr = NonConfidentialMemoryAddress::new(self.tsm_info_address as *mut usize)?;
        let ptr_end = NonConfidentialMemoryAddress::new((self.tsm_info_address + self.tsm_info_len) as *mut usize)?.as_ptr();
        unsafe {
            ptr.write(0x00010002);
            ptr = ptr.add(8, ptr_end)?;
            ptr.write(0);
            ptr = ptr.add(8, ptr_end)?;
            ptr.write(32);
            ptr = ptr.add(8, ptr_end)?;
            ptr.write(32);
        }
        Ok(32)
    }
}
