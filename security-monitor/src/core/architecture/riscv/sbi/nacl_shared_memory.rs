// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GeneralPurposeRegister, GeneralPurposeRegisters};
use crate::core::memory_layout::{MemoryLayout, NonConfidentialMemoryAddress};
use crate::error::Error;

/// Represents the memory region shared between the hypervisor and the security monitor. The content of this memory region is structured
/// according to the RISC-V SBI NACL extension. The hypervisor and the security monitor use this memory region to exchange content of the
/// confidential hart state. Check the RISC-V CoVE spec for more information.
///
/// This memory region is owned by the hypervisor. Information passed through this memory region is untrusted. The hypervisor must set this
/// region before starting to use the security monitor. If the hypervisor does not setup this region, the security monitor will read only 0s
/// and will not write anything.
pub struct NaclSharedMemory {
    region: Option<(NonConfidentialMemoryAddress, NonConfidentialMemoryAddress)>,
}

// It is not safe to pass multable pointers in a multi-threaded application and this is what happens when we store NaclSharedMemory is the
// hardware hart. Despite this, we implement Send+Sync on NaclSharedMemory because Hardware hart is statically pinned (via assembly
// `mscratch`) to the physical hart executing the security monitor's code. The hypervisor still owns the entire memory region of the shared
// memory and we cannot rule out parallel writes this this shared memory. This is ok for us, because all reads and writes to this memory
// region are untrusted, volatile, and atomic.
unsafe impl Send for NaclSharedMemory {}
unsafe impl Sync for NaclSharedMemory {}

impl NaclSharedMemory {
    // Below constant is defined in the RISC-V SBI NACL extension spec.
    const SCRATCH_SPACE_SIZE: usize = 4096;
    // Below constant is defined in the RISC-V SBI NACL extension spec.
    const CSR_SPACE_SIZE: usize = 8 * 1024;

    pub fn uninitialized() -> Self {
        Self { region: None }
    }

    /// Sets up the NACL shared memory located in the non-confidential memory. Returns error if the NACL shared memory does not fit entirely
    /// in the non-confidential memory.
    pub fn set(&mut self, base_address: NonConfidentialMemoryAddress) -> Result<(), Error> {
        let nacl_shared_memory_size = Self::SCRATCH_SPACE_SIZE + Self::CSR_SPACE_SIZE;
        let end_address = MemoryLayout::read().non_confidential_address_at_offset(&base_address, nacl_shared_memory_size)?;
        self.region = Some((base_address, end_address));
        Ok(())
    }

    pub fn csr(&self, csr_code: usize) -> usize {
        self.read_at_offset(Self::SCRATCH_SPACE_SIZE + Self::csr_index(csr_code) * core::mem::size_of::<usize>())
    }

    pub fn write_csr(&self, csr_code: usize, value: usize) {
        self.write_at_offset(Self::SCRATCH_SPACE_SIZE + Self::csr_index(csr_code) * core::mem::size_of::<usize>(), value);
    }

    pub fn gpr(&self, gpr: GeneralPurposeRegister) -> usize {
        self.read_at_offset(core::mem::size_of::<usize>() * gpr.index())
    }

    pub fn write_gpr(&self, gpr: GeneralPurposeRegister, value: usize) {
        self.write_at_offset(core::mem::size_of::<usize>() * gpr.index(), value);
    }

    pub fn gprs(&self) -> GeneralPurposeRegisters {
        let mut gprs = GeneralPurposeRegisters::empty();
        GeneralPurposeRegisters::iter().for_each(|index| {
            let gpr = GeneralPurposeRegister::from_index(index).unwrap();
            let value = self.gpr(gpr);
            gprs.write(gpr, value);
        });
        gprs
    }

    fn csr_index(csr_code: usize) -> usize {
        ((csr_code & 0xc00) >> 2) | (csr_code & 0xff)
    }

    /// Reads usize from the NACL shared memory at the given offset.
    ///
    /// # Safety
    ///
    /// Given offset must be a valid offset of an entry in the NACL shared memory.
    fn read_at_offset(&self, offset_in_bytes: usize) -> usize {
        match &self.region {
            Some((base_address, end_address)) => {
                // Below unwrap is ok, because the constructor ensures that the entire nacl shared memory is in the non-confidential memory
                unsafe {
                    let pointer = base_address.add(offset_in_bytes, end_address.as_ptr()).unwrap();
                    pointer.read()
                }
            }
            None => 0,
        }
    }

    /// Writes usize to the NACL shared memory at the given offset.
    ///
    /// # Safety
    ///
    /// Given offset must be a valid offset of an entry in the NACL shared memory.
    fn write_at_offset(&self, offset_in_bytes: usize, value: usize) {
        if let Some((base_address, end_address)) = &self.region {
            // Below unwrap is ok, because we make ensure in constructor that the entire nacl shared memory is in the non-confidential
            // memory
            unsafe {
                let pointer = base_address.add(offset_in_bytes, end_address.as_ptr()).unwrap();
                pointer.write(value)
            };
        }
    }
}
