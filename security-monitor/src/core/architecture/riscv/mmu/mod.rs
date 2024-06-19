// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::CSR;
use crate::core::memory_layout::NonConfidentialMemoryAddress;
use crate::error::Error;

pub use hgatp::{Hgatp, HgatpMode};
pub use page_size::PageSize;
pub use page_table::PageTable;
pub use paging_system::PagingSystem;
pub use shared_page::SharedPage;

mod hgatp;
mod page_size;
mod page_table;
mod page_table_entry;
mod page_table_level;
mod paging_system;
mod shared_page;
mod specification;

pub fn copy_mmu_configuration_from_non_confidential_memory(hgatp: &Hgatp) -> Result<PageTable, Error> {
    let paging_mode = hgatp.mode().ok_or_else(|| Error::UnsupportedPagingMode())?;
    let paging_system = PagingSystem::from(&paging_mode).ok_or_else(|| Error::UnsupportedPagingMode())?;
    let root_page_address = NonConfidentialMemoryAddress::new(hgatp.root_page_table_pointer())?;
    Ok(PageTable::copy_from_non_confidential_memory(root_page_address, paging_system, paging_system.levels())?)
}

pub fn enable_address_translation_and_protection(hgatp: &Hgatp) {
    use crate::core::architecture::CSR;
    // Enable MMU for HS,VS,VS,U modes. It is safe to invoke below code because we have access to this register (run in the M-mode) and
    // hgatp is the content of the HGATP register calculated by the security monitor when recreating page tables of a confidential
    // virtual machine that will get executed.
    CSR.hgatp.write(hgatp.bits());
}
