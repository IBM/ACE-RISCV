// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::symmetrical_multiprocessing::RemoteHfenceGvmaVmid;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::{is_bit_enabled, PageSize};
use crate::core::control_data::{
    ConfidentialHart, ConfidentialHartRemoteCommand, ConfidentialVmId, ConfidentialVmMmioRegion, ControlDataStorage,
};
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;

use core::mem;

pub struct MmioAccessFault {
    cause: usize,
    mtval: usize,
    mtinst: usize,
    fault_address: usize,
}

impl MmioAccessFault {
    pub const ADDRESS_ALIGNMENT: usize = mem::size_of::<usize>();

    pub fn new(cause: usize, mtval: usize, mtinst: usize, fault_address: usize) -> Self {
        Self { cause, mtval, mtinst, fault_address }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        match ControlDataStorage::try_confidential_vm_mut(confidential_flow.confidential_vm_id(), |mut confidential_vm| {
            let confidential_vm_physical_address = ConfidentialVmPhysicalAddress::new(self.fault_address);
            let page_size = confidential_vm.memory_protector_mut().map_empty_page(confidential_vm_physical_address, PageSize::Size4KiB)?;
            let request = RemoteHfenceGvmaVmid::all_harts(None, page_size, confidential_flow.confidential_vm_id());
            confidential_flow
                .broadcast_remote_command(&mut confidential_vm, ConfidentialHartRemoteCommand::RemoteHfenceGvmaVmid(request))?;
            Ok(())
        }) {
            Ok(_) => confidential_flow.resume_confidential_hart_execution(),
            Err(_) => confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::MmioAccessFault(self)),
        }
    }

    pub fn apply_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        let instruction = self.mtinst | 0x3;
        let instruction_length = if is_bit_enabled(self.mtinst, 1) { riscv_decode::instruction_length(instruction as u16) } else { 2 };
        let mepc = confidential_hart.csrs().mepc.read_from_main_memory() + instruction_length;
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
