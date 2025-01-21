// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use crate::confidential_flow::handlers::mmio::add_mmio_region::AddMmioRegion;
pub use crate::confidential_flow::handlers::mmio::mmio_access_fault::MmioAccessFault;
pub use crate::confidential_flow::handlers::mmio::mmio_load_pending::MmioLoadPending;
pub use crate::confidential_flow::handlers::mmio::mmio_load_request::MmioLoadRequest;
pub use crate::confidential_flow::handlers::mmio::mmio_load_response::MmioLoadResponse;
pub use crate::confidential_flow::handlers::mmio::mmio_store_pending::MmioStorePending;
pub use crate::confidential_flow::handlers::mmio::mmio_store_request::MmioStoreRequest;
pub use crate::confidential_flow::handlers::mmio::mmio_store_response::MmioStoreResponse;
pub use crate::confidential_flow::handlers::mmio::remove_mmio_region::RemoveMmioRegion;

mod add_mmio_region;
mod mmio_access_fault;
mod mmio_load_pending;
mod mmio_load_request;
mod mmio_load_response;
mod mmio_store_pending;
mod mmio_store_request;
mod mmio_store_response;
mod remove_mmio_region;

core::arch::global_asm!(
    r#"
.attribute arch, "rv64gc"
.option norvc
.text

.align 4
.global _load_u64_from_confidential_vm_memory
_load_u64_from_confidential_vm_memory:
    lui   a1, 0xa0
    csrs  mstatus, a1
    ld    a2, (a0)
    csrc  mstatus, a1
    addi   a0, a2, 0
    ret
"#
);

extern "C" {
    fn _load_u64_from_confidential_vm_memory(address: usize) -> usize;
}

pub fn read_trapped_instruction(confidential_hart: &crate::core::control_data::ConfidentialHart) -> (usize, usize) {
    match confidential_hart.csrs().mtinst.read() {
        0 => {
            let guest_virtual_address = confidential_hart.csrs().mepc.read_from_main_memory();
            let mut low = unsafe { _load_u64_from_confidential_vm_memory(guest_virtual_address & !7) };
            low = low >> (8 * (guest_virtual_address & 7));
            let instruction_length = riscv_decode::instruction_length(low as u16);
            let mut high = 0;
            if instruction_length > (8 - (guest_virtual_address & 7)) {
                high = unsafe { _load_u64_from_confidential_vm_memory((guest_virtual_address + 7) & !7) };
                high = high << (8 * (8 - (guest_virtual_address & 7)));
            }
            (low | high, instruction_length)
        }
        mtinst => {
            let instruction = mtinst | 0x3;
            let instruction_length =
                if crate::core::architecture::is_bit_enabled(mtinst, 1) { riscv_decode::instruction_length(instruction as u16) } else { 2 };
            (instruction, instruction_length)
        }
    }
}
