// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::memory_layout::MemoryLayout;
use crate::core::memory_protector::{iopmp, pmp};
use crate::error::Error;

/// Exposes an interface to configure the hardware memory isolation component to
/// set memory access protection preventing the hypervisor from accessing memory it does not own
pub struct HypervisorMemoryProtector {}

impl HypervisorMemoryProtector {
    pub fn create() -> Self {
        Self {}
    }

    /// Configures the memory protection mechanism on the hart which executes this function.  
    pub fn setup(&self) -> Result<(), Error> {
        // We use RISC-V PMP mechanism to define that the confidential memory region is not accessible.
        // We use RISC-V IOPMP mechanism to ensure that no IO devices can access confidential memory region.
        let (confidential_memory_start, confidential_memory_end) = MemoryLayout::read().confidential_memory_boundary();
        pmp::split_memory_into_confidential_and_non_confidential(confidential_memory_start, confidential_memory_end)?;
        iopmp::protect_confidential_memory_from_io_devices(confidential_memory_start, confidential_memory_end)?;

        Ok(())
    }

    /// Reconfigures hardware to enable access initiated from this physical hart to memory regions
    /// owned by the hypervisor and denies accesses to all other memory regions.
    ///
    /// # Safety
    ///
    /// Caller must guarantee that the security monitor will transition in the finite state machine
    /// to the `non-confidential flow` and eventually to the hypervisor code.
    pub unsafe fn enable(&self, hgatp: usize) {
        pmp::close_access_to_confidential_memory();
        // Enable MMU for HS,VS,VS,U modes. It is safe to invoke below code because we have access
        // to this register (run in the M-mode) and hgatp is the content of the HGATP register
        // that the hypervisor used when it invoked the security monitor.
        unsafe {
            riscv::register::hgatp::write(hgatp);
            core::arch::asm!("hfence.gvma");
            core::arch::asm!("hfence.vvma");
        };
    }
}