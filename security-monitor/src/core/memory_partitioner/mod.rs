// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use confidential_memory_address::ConfidentialMemoryAddress;
pub use mmu::{PageSize, PagingSystem, RootPageTable};
pub use non_confidential_memory_address::NonConfidentialMemoryAddress;

use crate::error::{Error, InitType, NOT_INITIALIZED_CONFIDENTIAL_MEMORY};
use pointers_utility::{ptr_align, ptr_byte_add_mut, ptr_byte_offset};
use spin::Once;

mod confidential_memory_address;
mod iopmp;
mod mmu;
mod non_confidential_memory_address;
mod pmp;

/// MEMORY_PARTITIONER is a global variable that is set during the boot process by the initialization function
/// and never changes later -- this is guaranteed by Once<>.
static MEMORY_PARTITIONER: Once<MemoryPartitioner> = Once::new();

/// Partitions memory in the confidential and non-confidential memory regions using hardware mechanisms.
/// Exposes safe interface to reconfigure access permissions to memory regions for access initiated from the
/// physical hart to memory regions owned by the hypervisor or a confidential VM.
///
/// It also provides an interface to offset addresses while ensuring that the returned address remains inside
/// the same memory region, i.e., confidential or non-confidential memory.
pub struct MemoryPartitioner {
    non_confidential_memory_start: *mut usize,
    non_confidential_memory_end: *const usize,
    confidential_memory_start: *mut usize,
    confidential_memory_end: *const usize,
}

/// We need to declare Send+Sync on the `MemoryPartitioner` because MemoryPartitioner stores internally
/// raw pointers that are not safe to pass in a multi-threaded program. This is not a case
/// for MemoryPartitioner because we never expose raw pointers outside the MemoryPartitioner except for the
/// constructor when we return the initial address of the confidential memory. The constructor
/// is invoked only once by the initialization procedure during the boot of the system.
unsafe impl Send for MemoryPartitioner {}
unsafe impl Sync for MemoryPartitioner {}

impl MemoryPartitioner {
    /// Constructs the `MemoryPartitioner` where the confidential memory is within the memory range defined
    /// by `confidential_memory_start` and `confidential_memory_end`. Returns the `MemoryPartitioner` and
    /// the first alligned address in the confidential memory.
    ///
    /// # Safety
    ///
    /// This function must be called only once by the initialization procedure during the
    /// boot of the system.
    pub fn init(
        non_confidential_memory_start: *mut usize, non_confidential_memory_end: *const usize,
        confidential_memory_start: *mut usize, mut confidential_memory_end: *const usize,
    ) -> Result<(ConfidentialMemoryAddress, *const usize), Error> {
        assert!((non_confidential_memory_start as *const usize) < non_confidential_memory_end);
        assert!(non_confidential_memory_end <= (confidential_memory_start as *const usize));
        assert!((confidential_memory_start as *const usize) < confidential_memory_end);

        // We align the start of the confidential memory to the smalles possible page size (4KiB on RISC-V)
        // and make sure that its size is the multiply of this page size.
        let smalles_page_size_in_bytes = PageSize::smallest().in_bytes();
        let confidential_memory_start =
            ptr_align(confidential_memory_start, smalles_page_size_in_bytes, confidential_memory_end)
                .map_err(|_| Error::Init(InitType::NotEnoughMemory))?;
        // Let's make sure that the end of the confidential memory is properly aligned.
        let memory_size = ptr_byte_offset(confidential_memory_end, confidential_memory_start);
        let memory_size = usize::try_from(memory_size).map_err(|_| Error::Init(InitType::NotEnoughMemory))?;
        let number_of_pages = memory_size / smalles_page_size_in_bytes;
        let memory_size_in_bytes = number_of_pages * smalles_page_size_in_bytes;
        if memory_size > memory_size_in_bytes {
            // we must modify the end_address because the current one is not a multiply of the smallest page size
            confidential_memory_end =
                ptr_byte_add_mut(confidential_memory_start, memory_size_in_bytes, confidential_memory_end)?;
        }

        MEMORY_PARTITIONER.call_once(|| MemoryPartitioner {
            non_confidential_memory_start,
            non_confidential_memory_end,
            confidential_memory_start,
            confidential_memory_end,
        });

        // Reconfigure hardware to isolate the confidential memory region
        let confidential_memory_start = ConfidentialMemoryAddress::new(confidential_memory_start);
        pmp::split_memory_into_confidential_and_non_confidential(&confidential_memory_start, confidential_memory_end)?;
        iopmp::protect_confidential_memory_from_io_devices(&confidential_memory_start, confidential_memory_end)?;

        Ok((confidential_memory_start, confidential_memory_end))
    }

    /// Returns a an address in the confidential memory offset by given number of bytes from the
    /// initial address. Returns an error if the resulting address is outside the confidential memory.
    pub fn confidential_address_at_offset(
        &self, address: &ConfidentialMemoryAddress, offset_in_bytes: usize,
    ) -> Result<ConfidentialMemoryAddress, Error> {
        let incremented_address = unsafe { address.add(offset_in_bytes, self.confidential_memory_end) }
            .map_err(|_| Error::MemoryAccessAuthorization())?;
        Ok(incremented_address)
    }

    /// Returns a an address in the confidential memory offset by given number of bytes from the
    /// initial address and not exceeding given upper bound. Returns an error if the resulting address
    /// is outside the confidential memory or give upped bound.
    pub fn confidential_address_at_offset_bounded(
        &self, address: &ConfidentialMemoryAddress, offset_in_bytes: usize, upper_bound: *const usize,
    ) -> Result<ConfidentialMemoryAddress, Error> {
        assure!(upper_bound <= self.confidential_memory_end, Error::MemoryAccessAuthorization())?;
        Ok(self.confidential_address_at_offset(address, offset_in_bytes)?)
    }

    /// Returns a an address in the non-confidential memory offset by given number of bytes from the
    /// initial address. Returns an error if the resulting address is outside the non-confidential memory.
    pub fn non_confidential_address_at_offset(
        &self, address: &NonConfidentialMemoryAddress, offset_in_bytes: usize,
    ) -> Result<NonConfidentialMemoryAddress, Error> {
        let incremented_address = unsafe { address.add(offset_in_bytes, self.non_confidential_memory_end) }
            .map_err(|_| Error::MemoryAccessAuthorization())?;
        Ok(incremented_address)
    }

    /// Checks if the raw pointer is inside the non-confidential memory.
    pub fn is_in_non_confidential_range(&self, address: *const usize) -> bool {
        self.non_confidential_memory_start as *const usize <= address && address < self.non_confidential_memory_end
    }

    /// Clears all confidential memory, writting to it 0s.
    ///
    /// # Safety
    ///
    /// Caller must guarantee that there is no other thread that can write to confidential memory during execution
    /// of this function.
    pub unsafe fn clear_confidential_memory(&self) {
        // we can safely cast below offset to usize because the constructor guarantees that the confidential memory
        // range is valid, and so the memory size must be a valid usize
        let memory_size = ptr_byte_offset(self.confidential_memory_end, self.confidential_memory_start) as usize;
        let usize_alligned_offsets = (0..memory_size).step_by(core::mem::size_of::<usize>());
        usize_alligned_offsets.for_each(|offset_in_bytes| {
            if let Ok(ptr) =
                ptr_byte_add_mut(self.confidential_memory_start, offset_in_bytes, self.confidential_memory_end)
            {
                unsafe { ptr.write_volatile(0) };
            }
        });
    }

    /// Reconfigures hardware to enable access initiated from this physical hart to memory regions
    /// owned by the confidential VM and deny access to all other memory regions.
    ///
    /// # Arguments
    ///
    /// `hgatp` must be a valid value of the RISC-V hgatp register that contains CVM's id and the address
    /// of the root page table for the 2nd level addres translation.
    ///
    /// # Safety
    ///
    /// Caller must guarantee that the security monitor will transition in the finite state machine
    /// to the `confidential flow` and that the hgatp argument contains the correct id and the root
    /// page table address of the confidential VM that will be executed next.
    pub unsafe fn enable_confidential_vm_memory_view(hgatp: usize) {
        pmp::open_access_to_confidential_memory();
        // Enable MMU for HS,VS,VS,U modes. It is safe to invoke below code
        // because we have access to this register (run in the M-mode) and
        // hgatp is the content of the HGATP register calculated by the security monitor
        // when recreating page tables of a confidential virtual machine that will
        // get executed.
        unsafe {
            riscv::register::hgatp::write(hgatp);
            core::arch::asm!("hfence.gvma");
            core::arch::asm!("hfence.vvma");
        };
    }

    /// Reconfigures hardware to enable access initiated from this physical hart to memory regions
    /// owned by the hypervisor and denies accesses to all other memory regions.
    ///
    /// # Safety
    ///
    /// Caller must guarantee that the security monitor will transition in the finite state machine
    /// to the `non-confidential flow` and eventually to a hypervisor code.
    pub unsafe fn enable_hypervisor_memory_view() {
        pmp::close_access_to_confidential_memory();
        // mmu will be reconfigured by the context switch code (assembly) that restores the previous
        // hgatp value that the hypervisor used when it invoked a security monitor's call.
    }

    pub fn get() -> &'static MemoryPartitioner {
        MEMORY_PARTITIONER.get().expect(NOT_INITIALIZED_CONFIDENTIAL_MEMORY)
    }
}
