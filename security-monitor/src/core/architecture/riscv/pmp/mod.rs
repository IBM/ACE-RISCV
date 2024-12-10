// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::specification::{
    PMP_ADDRESS_SHIFT, PMP_CONFIG_SHIFT, PMP_OFF_MASK, PMP_PERMISSION_RWX_MASK, PMP_TOR_MASK,
};
use crate::core::architecture::CSR;
use crate::error::Error;

// OpenSBI set already PMPs to isolate OpenSBI firmware from the rest of the
// system PMP0 protects OpenSBI memory region while PMP1 defines the system
// range We will use PMP0 and PMP1 to protect the confidential memory region,
// PMP2 to protect the OpenSBI, and PMP3 to define the system range.
pub fn split_memory_into_confidential_and_non_confidential(
    confidential_memory_start: usize, confidential_memory_end: usize,
) -> Result<(), Error> {
    // TODO: read how many PMPs are supported
    const MINIMUM_NUMBER_OF_PMP_REQUIRED: usize = 4;
    let number_of_pmps = 16;
    debug!("Number of PMPs={}", number_of_pmps);
    ensure!(number_of_pmps >= MINIMUM_NUMBER_OF_PMP_REQUIRED, Error::NotEnoughPmps())?;

    // TODO: simplify use of PMP by using a single PMP entry to isolate the confidential memory.
    // We assume here that the first two PMPs are not used by anyone else, e.g., OpenSBI firmware
    // CSR.pmpaddr0.write(confidential_memory_start >> PMP_ADDRESS_SHIFT);
    // CSR.pmpaddr1.write(confidential_memory_end >> PMP_ADDRESS_SHIFT);
    CSR.pmpaddr0.write(0);
    CSR.pmpaddr1.write(0);

    close_access_to_confidential_memory();
    crate::debug::__print_pmp_configuration();
    Ok(())
}

pub fn open_access_to_confidential_memory() {
    // if CSR.mseccfg.read() & MSECCFG_MML > 0 {
    //     assert!(CSR.mseccfg.read() & mseccfg.RLB > 0); // we require RLB so we can set and unset the L bit.
    //     let mask = PMP_PERMISSION_L_MASK | mask << (1 * PMP_CONFIG_SHIFT);
    //     CSR.pmpcfg0.read_and_clear_bits(mask); // remove L bit means in Smepmp that the rule is enforced for non M-mode software
    // } else {
    //     let mask = (PMP_OFF_MASK | PMP_PERMISSION_RWX_MASK) | (PMP_TOR_MASK | PMP_PERMISSION_RWX_MASK) << (1 * PMP_CONFIG_SHIFT);
    //     CSR.pmpcfg0.read_and_set_bits(mask); // assign access permissions to confidential memory
    // }
    // clear_caches();
}

pub fn close_access_to_confidential_memory() {
    // if CSR.mseccfg.read() & MSECCFG_MML > 0 {
    //     assert!(CSR.mseccfg.read() & mseccfg.RLB > 0); // we require RLB so we can set and unset the L bit.
    //     let mask = PMP_PERMISSION_L_MASK | mask << (1 * PMP_CONFIG_SHIFT);
    //     CSR.pmpcfg0.read_and_set_bits(mask);  // setting L bit means in Smepmp that the rule is enforced for M-mode software
    // } else {
    //     let mask = PMP_PERMISSION_RWX_MASK | (PMP_PERMISSION_RWX_MASK << (1 * PMP_CONFIG_SHIFT));
    //     CSR.pmpcfg0.read_and_clear_bits(mask); // clear access permissions to confidential memory
    // }
    // clear_caches();
}

fn clear_caches() {
    // See Section 3.7.2 of RISC-V privileged specification v1.12.
    // PMP translations can be cached and address translation can be done speculatively. Thus, it is adviced to flush caching structures.
    super::fence::sfence_vma();
    super::fence::hfence_gvma();
}
