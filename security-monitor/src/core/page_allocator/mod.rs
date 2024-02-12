// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use page::{Allocated, Page, PageState, UnAllocated};
pub use page_allocator::PageAllocator;
pub use shared_page::SharedPage;

mod page;
mod page_allocator;
mod shared_page;
