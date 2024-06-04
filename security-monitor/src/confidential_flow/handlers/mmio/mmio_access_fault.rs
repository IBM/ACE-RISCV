// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ConfidentialHart, ConfidentialVmId, ConfidentialVmMmioRegion, ControlDataStorage};
use core::mem;

pub struct MmioAccessFault {
    cause: usize,
    mtval: usize,
    instruction_length: usize,
}

impl MmioAccessFault {
    pub const ADDRESS_ALIGNMENT: usize = mem::size_of::<usize>();

    pub fn new(cause: usize, mtval: usize, instruction_length: usize) -> Self {
        Self { cause, mtval, instruction_length }
    }

    pub fn apply_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        let mepc = confidential_hart.csrs().mepc.read_from_main_memory() + self.instruction_length;
        confidential_hart.csrs_mut().vsepc.write(mepc);
        let trap_vector_address = confidential_hart.csrs().vstvec.read();
        confidential_hart.csrs_mut().mepc.save_value_in_main_memory(trap_vector_address);
        confidential_hart.csrs_mut().vscause.write(self.cause);
        confidential_hart.csrs_mut().vstval.write(self.mtval);
    }

    pub fn tried_to_access_valid_mmio_region(confidential_vm_id: ConfidentialVmId, fault_address: usize) -> bool {
        ControlDataStorage::try_confidential_vm(confidential_vm_id, |confidential_vm| {
            Ok(confidential_vm.is_mmio_region_defined(&ConfidentialVmMmioRegion::new(fault_address, Self::ADDRESS_ALIGNMENT)))
        })
        .unwrap_or(false)
    }
}
