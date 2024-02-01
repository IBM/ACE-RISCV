// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::{Error, HardwareFeatures};
use riscv::register::{pmpaddr0, pmpaddr1, pmpcfg0, Permission, Range};

/// constant specified in the RISC-V spec
const PMP_SHIFT: u16 = 2;

// OpenSBI set already PMPs to isolate OpenSBI firmware from the rest of the
// system PMP0 protects OpenSBI memory region while PMP1 defines the system
// range We will use PMP0 and PMP1 to protect the confidential memory region,
// PMP2 to protect the OpenSBI, and PMP3 to define the system range.
pub(super) fn split_memory_into_confidential_and_non_confidential(
    confidential_memory_start: usize, confidential_memory_end: usize,
) -> Result<(), Error> {
    // TODO: read how many PMPs are supported
    const MINIMUM_NUMBER_OF_PMP_REQUIRED: usize = 4;
    let number_of_pmps = 16;
    debug!("Number of PMPs={}", number_of_pmps);
    assure!(number_of_pmps >= MINIMUM_NUMBER_OF_PMP_REQUIRED, Error::NotSupportedHardware(HardwareFeatures::NotEnoughPmps))?;

    // TODO: simplify use of PMP by using a single PMP entry to isolate the confidential memory.
    // We assume here that the first two PMPs are not used by anyone else, e.g., OpenSBI firmware
    unsafe {
        pmpaddr0::write(confidential_memory_start >> PMP_SHIFT);
        pmpcfg0::set_pmp(0, Range::OFF, Permission::NONE, false);

        pmpaddr1::write(confidential_memory_end >> PMP_SHIFT);
        pmpcfg0::set_pmp(1, Range::TOR, Permission::NONE, false);
    }
    clear_caches();

    crate::debug::__print_pmp_configuration();
    Ok(())
}

pub unsafe fn open_access_to_confidential_memory() {
    pmpcfg0::set_pmp(0, Range::OFF, Permission::RWX, false);
    pmpcfg0::set_pmp(1, Range::TOR, Permission::RWX, false);
    clear_caches();
}

pub unsafe fn close_access_to_confidential_memory() {
    // TODO: simplify use of PMPs so we just need one PMP register to
    // split memory into confidential and non-confidential regions
    pmpcfg0::set_pmp(0, Range::OFF, Permission::NONE, false);
    pmpcfg0::set_pmp(1, Range::TOR, Permission::NONE, false);
    clear_caches();
}

fn clear_caches() {
    // See Section 3.7.2 of RISC-V privileged specification v1.12.
    // PMP translations can be cached and address translation can be done speculatively. Thus, it is adviced to flush caching structures.
    unsafe {
        riscv::asm::sfence_vma_all();
        // TODO: flush caches of the guest mode
        // hfence_gvma_all();
    }
}
