// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use page_size::PageSize;
pub use page_table::RootPageTable;
pub use paging_system::PagingSystem;

mod page_size;
mod page_table;
mod page_table_entry;
mod page_table_memory;
mod paging_system;

// use crate::error::Error;
//
// pub fn virtual_to_physical(root: &PageTable, virtual_address: usize) ->
// Result<Option<usize>, Error> {     use core::ops::Add;
//     const PAGE_OFFSET_MASK: usize = 0xfff;

//     let vpn = root.kind().vpn(virtual_address, root.level());
//     let mut entry = root.entry(vpn).ok_or_else(||
// Error::PageTableConfiguration())?;     for level in
// (0..=root.kind().levels()).rev() {         if level == 0 {
//             return Ok(None);
//         }
//         if !entry.is_valid() {
//             // PageFault
//             break;
//         }
//         let address = entry.address();

//         if entry.is_leaf() {
//             let page_offset = virtual_address & PAGE_OFFSET_MASK;
//             return Ok(Some(address | page_offset));
//         }
//         let next_vpn = root.kind().vpn(virtual_address, level - 1);
//         let next_entry_ptr = address.add(8 * next_vpn) as *const
// PageTableEntry;         entry = unsafe { next_entry_ptr.as_ref().unwrap() };
//     }

//     Ok(None)
// }
