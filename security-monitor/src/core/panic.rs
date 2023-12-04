// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::pmp::MemoryLayout;

/// This piece of code executes on a panic. Panic is a runtime error that
/// indicates an implementation bug from which we cannot recover. Examples are
/// integer overflow, asserts, explicit statements like panic!(), unwrap(),
/// expect().
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    debug!("Ops security monitor panicked!");
    if let Some(p) = info.location() {
        debug!("Line {}, file {}: {}", p.line(), p.file(), info.message().unwrap());
    } else {
        debug!("no information available.");
    }
    debug!("Cleaning up...");
    // Clear the content of the confidential memory.
    // Safety: The initialization of the confidential memory guarantees that this memory
    // region is aligned to the smalles possible page size, thus it is aligned to usize.
    // Also the size of the memory is a multiply of usize, so below code will never write
    // outside the confidential memory region.
    MemoryLayout::get().clear_confidential_memory();

    // sleep or loop forever since there is nothing else we can do
    loop {
        unsafe {
            core::arch::asm!("wfi");
        }
    }
}
