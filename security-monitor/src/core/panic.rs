// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_tracker::CONFIDENTIAL_MEMORY_RANGE;
use crate::error::NOT_INITIALIZED_CONFIDENTIAL_MEMORY;

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
    // clear the content of the confidential memory
    CONFIDENTIAL_MEMORY_RANGE.get().expect(NOT_INITIALIZED_CONFIDENTIAL_MEMORY).clone().for_each(|address| {
        unsafe { (address as *mut u8).write_volatile(0) };
    });

    // sleep or loop forever since there is nothing else we can do
    loop {
        unsafe {
            core::arch::asm!("wfi");
        }
    }
}
