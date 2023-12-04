// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use confidential_memory_address::ConfidentialMemoryAddress;
pub use memory_layout::{MemoryLayout, MEMORY_LAYOUT};
pub use non_confidential_memory_address::NonConfidentialMemoryAddress;

mod confidential_memory_address;
mod memory_layout;
mod non_confidential_memory_address;

pub fn open_access_to_confidential_memory() {
    use riscv::register::{pmpcfg0, Permission, Range};
    unsafe {
        pmpcfg0::set_pmp(0, Range::OFF, Permission::RWX, false);
        pmpcfg0::set_pmp(1, Range::TOR, Permission::RWX, false);
        pmpcfg0::set_pmp(2, Range::NAPOT, Permission::RWX, false);
        riscv::asm::sfence_vma_all();
    }
}

pub fn close_access_to_confidential_memory() {
    // TODO: simplify use of PMPs so we just need one PMP register to
    // split memory into confidential and non-confidential regions
    use riscv::register::{pmpcfg0, Permission, Range};
    unsafe {
        pmpcfg0::set_pmp(0, Range::OFF, Permission::NONE, false);
        pmpcfg0::set_pmp(1, Range::TOR, Permission::NONE, false);
        pmpcfg0::set_pmp(2, Range::NAPOT, Permission::NONE, false);
        riscv::asm::sfence_vma_all();
        // HFENCE.GVMA rs1=0 rs2=0 according to the spec 8.5.3
    }
}
