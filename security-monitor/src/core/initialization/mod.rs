// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ControlData, HardwareHart, CONTROL_DATA};
use crate::core::memory_layout::{ConfidentialMemoryAddress, MemoryLayout};
use crate::core::memory_protector::{HypervisorMemoryProtector, PageSize};
use crate::core::memory_tracker::{MemoryTracker, Page, UnAllocated, MEMORY_TRACKER};
use crate::error::{Error, HardwareFeatures, InitType, NOT_INITIALIZED_HART, NOT_INITIALIZED_HARTS};
use alloc::vec::Vec;
use core::mem::size_of;
use fdt::Fdt;
use pointers_utility::ptr_byte_add_mut;
use spin::{Mutex, Once, RwLock};

extern "C" {
    fn enter_from_hypervisor_or_vm_asm() -> !;
}

/// A *private* static array of hart states stores the hypervisor's harts states. Safe Rust code cannot access this
/// structure. We store the memory addresses of individual HardwareHart structure in the mscratch register. Thus, the
/// assembly code of the context switch can store and load data from this data structure.
///
/// # Safety
///
/// Initialization procedure must guarantee that the mscratch register contains the address of the memory region that
/// stores the state of the executing hart.
static HARTS_STATES: Once<Mutex<Vec<HardwareHart>>> = Once::new();

/// The entry point to the security monitor initialization procedure. It should be called by the booting firmware (e.g.,
/// OpenSBI) during the boot process to initialize ACE. After the return, the control flow returns to the booting
/// firmware, which eventually passes the execution control to untrusted code (hypervisor). After the return of this
/// function, the security properties of ACE hold.
#[no_mangle]
extern "C" fn init_security_monitor_asm(flattened_device_tree_address: *const u8) {
    debug!("initializing the ACE extension");
    if let Err(error) = init_security_monitor(flattened_device_tree_address) {
        debug!("Failed to initialize the ACE extension: {:?}", error);
    }
}

/// Initializes the security monitor.
///
/// # Safety
///
/// Caller must pass a valid pointer to the flattened device tree. The content of the flattened device tree is trusted.
fn init_security_monitor(flattened_device_tree_address: *const u8) -> Result<(), Error> {
    let fdt = unsafe { Fdt::from_ptr(flattened_device_tree_address)? };

    // TODO: make sure the system has enough physical memory
    let (confidential_memory_start, confidential_memory_end) = initialize_memory_layout(&fdt)?;

    // Create page tokens, heap, memory tracker
    initalize_security_monitor_state(confidential_memory_start, confidential_memory_end)?;

    let number_of_harts = verify_harts(&fdt)?;

    // Prepares memory required to store physical hart state
    prepare_harts(number_of_harts)?;
    setup_this_hart()?;

    // if we reached this line, then the security monitor has been correctly
    // initialized.
    Ok(())
}

/// Parses the flattened device tree (FDT) and reads the number of physical harts in the system. It verifies that these
/// harts support extensions required by ACE. Error is returned if FDT is incorrectly structured or exist a hart that
/// does not support required extensions.
fn verify_harts(fdt: &Fdt) -> Result<usize, Error> {
    const RISCV_ARCH: &str = "rv64";
    const ATOMIC_EXTENSION: char = 'a';
    const HYPERVISOR_EXTENSION: char = 'h';
    const FDT_RISCV_ISA: &str = "riscv,isa";
    let required_extensions = &[ATOMIC_EXTENSION, HYPERVISOR_EXTENSION];

    // Assumption: all harts in the system can run the security monitor
    // and thus we expect that everyone hart implements all required features
    for (cpu_id, cpu) in fdt.cpus().enumerate() {
        // example riscv,isa value: rv64imafdch_zicsr_zifencei_zba_zbb_zbc_zbs
        let isa = cpu.property(FDT_RISCV_ISA).ok_or(Error::FdtParsing())?.as_str().unwrap_or("");
        let extensions = &isa.split('_').next().unwrap_or(&"")[RISCV_ARCH.len()..];
        debug!("Hart #{}: {:?}", cpu_id, isa);

        // make sure the CPU has the required architecture
        assure!(isa.starts_with(RISCV_ARCH), Error::NotSupportedHardware(HardwareFeatures::InvalidCpuArch))?;
        // make sure the CPU supports all required ISA extensions
        required_extensions.into_iter().try_for_each(|ext| {
            assure!(extensions.contains(*ext), Error::NotSupportedHardware(HardwareFeatures::NoCpuExtension(*ext)))
        })?;
    }

    Ok(fdt.cpus().count())
}

fn initialize_memory_layout(fdt: &Fdt) -> Result<(ConfidentialMemoryAddress, *const usize), Error> {
    // TODO: FDT may contain multiple regions. For now, we assume there is only one region in the FDT.
    // This assumption is fine for the emulated environment (QEMU).
    let fdt_memory_region = fdt.memory().regions().next().ok_or(Error::Init(InitType::FdtMemory))?;
    // Safety: We own all the memory because we are early in the boot process and have full rights
    // to split memory according to our needs. Thus, it is fine to cast `usize` to `*mut usize`
    // Information read from FDT is trusted. So we trust that we read the correct start and size of the
    // memory.
    let memory_start = fdt_memory_region.starting_address as *mut usize;
    // In assembly that executed this initialization function splitted the memory into two regions where
    // the second region's size is equal or greater than the first ones.
    let non_confidential_memory_size = fdt_memory_region.size.unwrap_or(0);
    let confidential_memory_size = non_confidential_memory_size;
    let memory_size = non_confidential_memory_size + confidential_memory_size;
    let memory_end = memory_start.wrapping_byte_add(memory_size) as *const usize;
    debug!("Memory {:#?}-{:#?}", memory_start, memory_end);

    // First region of memory is defined as non-confidential memory
    let non_confidential_memory_start = memory_start;
    let non_confidential_memory_end =
        ptr_byte_add_mut(non_confidential_memory_start, non_confidential_memory_size, memory_end)
            .map_err(|_| Error::Init(InitType::MemoryBoundary))?;
    debug!("Non-confidential memory {:#?}-{:#?}", non_confidential_memory_start, non_confidential_memory_end);

    // Second region of memory is defined as confidential memory
    let confidential_memory_start = non_confidential_memory_end;
    let confidential_memory_end = memory_end;
    debug!("Confidential memory {:#?}-{:#?}", confidential_memory_start, confidential_memory_end);

    let (confidential_memory_address_start, confidential_memory_address_end) = unsafe {
        MemoryLayout::init(
            non_confidential_memory_start,
            non_confidential_memory_end,
            confidential_memory_start,
            confidential_memory_end,
        )
    }?;

    Ok((confidential_memory_address_start, confidential_memory_address_end))
}

/// This function is called only once during the initialization of the security
/// monitor during the boot process. This function initializes secure monitor's
/// memory management like allocators.
fn initalize_security_monitor_state(
    confidential_memory_start: ConfidentialMemoryAddress, confidential_memory_end: *const usize,
) -> Result<(), Error> {
    const NUMBER_OF_HEAP_PAGES: usize = 4 * 1024;
    // Safety: initialization order is crucial for safety because at some point we
    // start allocating objects on heap, e.g., page tokens. We have to first
    // initialize the global allocator, which permits us to use heap. To initialize heap
    // we need to decide what is the confidential memory address range and split this memory
    // into regions owned by heap allocator and page allocator (memory tracker).
    let confidential_memory_size = confidential_memory_start.offset_from(confidential_memory_end);
    let number_of_pages = usize::try_from(confidential_memory_size)? / PageSize::smallest().in_bytes();
    // calculate if we have enough memory in the system to store page tokens. In the worst case we
    // have one page token for every possible page in the confidential memory.
    let size_of_a_page_token_in_bytes = size_of::<Page<UnAllocated>>();
    let bytes_required_to_store_page_tokens = number_of_pages * size_of_a_page_token_in_bytes;
    let heap_pages = NUMBER_OF_HEAP_PAGES + (bytes_required_to_store_page_tokens / PageSize::smallest().in_bytes());
    assure!(number_of_pages > heap_pages, Error::Init(InitType::NotEnoughMemory))?;
    // Set up the global allocator so we can start using alloc::*.
    let heap_size_in_bytes = heap_pages * PageSize::smallest().in_bytes();
    let mut heap_start_address = confidential_memory_start;
    let heap_end_address =
        MemoryLayout::read().confidential_address_at_offset(&mut heap_start_address, heap_size_in_bytes)?;
    crate::core::heap::init_heap(heap_start_address, heap_size_in_bytes);

    // Memory tracker starts directly after the heap
    let memory_tracker_start_address = heap_end_address;
    assert!(memory_tracker_start_address.is_aligned_to(PageSize::smallest().in_bytes()));
    // Memory tracker takes ownership of the rest of the confidential memory.
    let memory_tracker_end_address = confidential_memory_end;
    // It is safe to construct the memory tracker because we own the corresponding memory region and pass this
    // ownership to the memory tracker.
    let memory_tracker = unsafe { MemoryTracker::new(memory_tracker_start_address, memory_tracker_end_address)? };
    MEMORY_TRACKER.call_once(|| RwLock::new(memory_tracker));
    CONTROL_DATA.call_once(|| RwLock::new(ControlData::new()));

    Ok(())
}

fn prepare_harts(number_of_harts: usize) -> Result<(), Error> {
    // we need to allocate stack for the dumped state of each physical HART.
    let mut harts_states = Vec::with_capacity(number_of_harts);
    for hart_id in 0..number_of_harts {
        let stack = MemoryTracker::acquire_continous_pages(1, PageSize::Size2MiB)?.remove(0);
        let hypervisor_memory_protector = HypervisorMemoryProtector::create();
        debug!("HART[{}] stack {:x}-{:x}", hart_id, stack.start_address(), stack.end_address());
        harts_states.insert(hart_id, HardwareHart::init(hart_id, stack, hypervisor_memory_protector));
    }
    HARTS_STATES.call_once(|| Mutex::new(harts_states));

    Ok(())
}

/// Enables entry points to the security monitor by taking control over some interrupts and protecting confidential
/// memory region using hardware isolation mechanisms.
fn setup_this_hart() -> Result<(), Error> {
    // Hypervisor handles all traps except two that might carry security monitor calls. These exceptions always trap in
    // the security monitor entry point of a non-confidential flow.
    unsafe {
        riscv::register::medeleg::clear_supervisor_env_call();
        riscv::register::medeleg::clear_virtual_supervisor_env_call();
    }

    // Set up the trap vector, so the above exceptions are handled by the security monitor.
    let trap_vector_address = (enter_from_hypervisor_or_vm_asm as usize)
        .try_into()
        .map_err(|_| Error::Init(InitType::InvalidAssemblyAddress))?;
    debug!("trap handler address: {:x}", trap_vector_address);
    unsafe {
        riscv::register::mtvec::write(trap_vector_address, riscv::register::mtvec::TrapMode::Direct);
    }

    // OpenSBI requires that mscratch points to an internal OpenSBI's structure. We have to store this pointer during
    // init and restore it every time we delegate exception/interrupt to the Sbi firmware (e.g., OpenSbi).
    let mut harts = HARTS_STATES.get().expect(NOT_INITIALIZED_HARTS).lock();
    let hart_id = riscv::register::mhartid::read();
    let hart = harts.get_mut(hart_id).expect(NOT_INITIALIZED_HART);

    // The mscratch must point to the memory region when the security monitor stores the dumped states of confidential
    // harts. This is crucial for context switches because assembly code will use the mscratch register to decide where
    // to store/load registers content. Below 'swap' stores pointer to opensbi_mscratch in the internal hart state.
    // OpenSBI stored in mscratch a pointer to the `opensbi_mscratch` region of this hart before calling the security
    // monitor's initialization procedure. Thus, the swap will move the mscratch register value into the dump state of
    // the hart
    hart.swap_mscratch();
    riscv::register::mscratch::write(hart.address());

    // Configure the memory isolation mechanism that can limit memory view of the hypervisor to the memory region owned
    // by the hypervisor. The setup method enables the memory isolation. It is safe to call it because the
    // `MemoryLayout` is initialized on the boot hart and this happens before the hart setup.
    unsafe {
        hart.hypervisor_memory_protector().setup()?;
    }

    Ok(())
}
