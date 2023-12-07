// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::{Error, HardwareFeatures};

// OpenSBI set already PMPs to isolate OpenSBI firmware from the rest of the
// system PMP0 protects OpenSBI memory region while PMP1 defines the system
// range We will use PMP0 and PMP1 to protect the confidential memory region,
// PMP2 to protect the OpenSBI, and PMP3 to define the system range.
pub(super) fn split_memory_into_confidential_and_non_confidential(
    confidential_memory_start: usize, confidential_memory_end: usize,
) -> Result<(), Error> {
    use riscv::register::{Permission, Range};

    const PMP_SHIFT: u16 = 2;

    // TODO: read how many PMPs are supported
    const MINIMUM_NUMBER_OF_PMP_REQUIRED: usize = 4;
    let number_of_pmps = 64;
    debug!("Number of PMPs={}", number_of_pmps);
    assure!(
        number_of_pmps >= MINIMUM_NUMBER_OF_PMP_REQUIRED,
        Error::NotSupportedHardware(HardwareFeatures::NotEnoughPmps)
    )?;

    // TODO: simplify to use a single PMP to isolate the confidential memory.
    // first shift PMP0, and PMP1 by two to make space for the confidential memory
    // PMPs
    let pmpcfg0 = riscv::register::pmpcfg0::read();
    let pmp0 = riscv::register::pmpaddr0::read();
    let pmp0cfg = pmpcfg0.into_config(0);
    let pmp1 = riscv::register::pmpaddr1::read();
    let pmp1cfg = pmpcfg0.into_config(1);
    unsafe {
        riscv::register::pmpaddr2::write(pmp0);
        riscv::register::pmpcfg0::set_pmp(2, pmp0cfg.range, pmp0cfg.permission, false);

        riscv::register::pmpaddr3::write(pmp1);
        riscv::register::pmpcfg0::set_pmp(3, pmp1cfg.range, pmp1cfg.permission, false);
    }

    // now set up PMP0 and PMP1 to define the range of the confidential memory
    unsafe {
        riscv::register::pmpaddr0::write(confidential_memory_start >> PMP_SHIFT);
        riscv::register::pmpcfg0::set_pmp(0, Range::OFF, Permission::NONE, false);

        riscv::register::pmpaddr1::write(confidential_memory_end >> PMP_SHIFT);
        riscv::register::pmpcfg0::set_pmp(1, Range::TOR, Permission::NONE, false);
        riscv::asm::sfence_vma_all();
    }

    crate::debug::__print_pmp_configuration();

    Ok(())
}

pub unsafe fn open_access_to_confidential_memory() {
    use riscv::register::{pmpcfg0, Permission, Range};
    pmpcfg0::set_pmp(0, Range::OFF, Permission::RWX, false);
    pmpcfg0::set_pmp(1, Range::TOR, Permission::RWX, false);
    pmpcfg0::set_pmp(2, Range::NAPOT, Permission::RWX, false);
    riscv::asm::sfence_vma_all();
}

pub unsafe fn close_access_to_confidential_memory() {
    // TODO: simplify use of PMPs so we just need one PMP register to
    // split memory into confidential and non-confidential regions
    use riscv::register::{pmpcfg0, Permission, Range};
    pmpcfg0::set_pmp(0, Range::OFF, Permission::NONE, false);
    pmpcfg0::set_pmp(1, Range::TOR, Permission::NONE, false);
    pmpcfg0::set_pmp(2, Range::NAPOT, Permission::NONE, false);
    riscv::asm::sfence_vma_all();
    // HFENCE.GVMA rs1=0 rs2=0 according to the spec 8.5.3
}
