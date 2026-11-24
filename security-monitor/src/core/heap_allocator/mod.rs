// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::ConfidentialMemoryAddress;
use crate::error::Error;

pub mod bitmap_allocator;
pub mod linked_list_allocator;
pub mod locked;

#[allow(unused_imports)]
pub use bitmap_allocator::BitmapAllocator;
#[allow(unused_imports)]
pub use linked_list_allocator::LinkedListAllocator;
pub use locked::Locked;

#[cfg(feature = "bitmap-allocator")]
#[global_allocator]
static HEAP_ALLOCATOR: Locked<BitmapAllocator> = Locked::new(BitmapAllocator::new());

#[cfg(not(feature = "bitmap-allocator"))]
#[global_allocator]
static HEAP_ALLOCATOR: Locked<LinkedListAllocator> = Locked::new(LinkedListAllocator::new());

pub(super) fn init_heap(start_address: ConfidentialMemoryAddress, end_address: ConfidentialMemoryAddress) -> Result<(), Error> {
    debug!("Heap {:x}-{:x}", start_address.as_usize(), end_address.as_usize());
    #[cfg(feature = "bitmap-allocator")]
    HEAP_ALLOCATOR.lock().init(start_address, end_address)?;

    #[cfg(not(feature = "bitmap-allocator"))]
    unsafe {
        let heap_size = end_address.as_usize().saturating_sub(start_address.as_usize());
        HEAP_ALLOCATOR.lock().add_free_region(start_address.as_usize(), heap_size);
    }
    Ok(())
}
