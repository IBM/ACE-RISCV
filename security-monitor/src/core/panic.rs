// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_partitioner::MemoryPartitioner;

/// This piece of code executes on a panic. Panic is a runtime error that
/// indicates an implementation bug from which we cannot recover. Examples are
/// integer overflow, asserts, explicit statements like panic!(), unwrap(),
/// expect().
///
/// This function halts all other harts in the system and clear the confidential memory.
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    // TODO: halt all other harts and make sure the below code executes exclusively on one hart
    debug!("Ops security monitor panicked!");
    if let Some(p) = info.location() {
        debug!("Line {}, file {}: {}", p.line(), p.file(), info.message().unwrap());
    } else {
        debug!("no information available.");
    }
    debug!("Cleaning up...");
    // Clear the content of the confidential memory.
    // Safety:
    // 1) The initialization of the confidential memory guarantees that this memory
    // region is aligned to the smalles possible page size, thus it is aligned to usize.
    // Also the size of the memory is a multiply of usize, so below code will never write
    // outside the confidential memory region.
    // 2) TODO: we must guarantee that only one hardware thread calls this method. Specifically
    // that there is no panic! executed on two different harts at the same time.
    unsafe { MemoryPartitioner::get().clear_confidential_memory() };

    // sleep or loop forever since there is nothing else we can do
    loop {
        unsafe {
            core::arch::asm!("wfi");
        }
    }
}
