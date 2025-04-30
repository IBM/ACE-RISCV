// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::fence::fence_wo;
use crate::core::architecture::riscv::specification::*;
use crate::core::architecture::{HardwareExtension, PageSize, CSR};
use crate::core::control_data::{ControlDataStorage, HardwareHart};
use crate::core::hardware_setup::HardwareSetup;
use crate::core::interrupt_controller::InterruptController;
use crate::core::memory_layout::{ConfidentialMemoryAddress, MemoryLayout};
use crate::core::memory_protector::HypervisorMemoryProtector;
use crate::core::page_allocator::{Page, PageAllocator, UnAllocated};
use crate::error::Error;
use alloc::vec::Vec;
use core::mem::size_of;
use flattened_device_tree::FlattenedDeviceTree;
use pointers_utility::ptr_byte_add_mut;
use spin::{Mutex, Once};

const NUMBER_OF_HEAP_PAGES: usize = 80 * 1024;

extern "C" {
    // Assembly function that is an entry point to the security monitor from the hypervisor or a virtual machine.
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
extern "C" fn init_security_monitor_asm(cold_boot: bool, flattened_device_tree_address: *const u8) {
    debug!("Initializing the CoVE security monitor for SiFive P550: v7");
    if cold_boot {
        if let Err(error) = init_security_monitor(flattened_device_tree_address) {
            // TODO: lock access to attestation keys/seed/credentials.
            debug!("Failed to initialize the security monitor: {:?}", error);
        } else {
            debug!("CoVE security monitor initialized successfully");
        }
    }
    use crate::core::architecture::HartArchitecturalState;
    let state = HartArchitecturalState::empty();
    crate::debug::__print_hart_state(&state);
}

/// Initializes the security monitor.
///
/// # Security
///
/// The input address points to the flattened device tree, which content is trusted.
///
/// # Safety
///
/// See `FlattenedDeviceTree::from_raw_pointer` for safety requirements.
fn init_security_monitor(flattened_device_tree_address: *const u8) -> Result<(), Error> {
    debug!("init_security_monitor: Read FDT...");
    let fdt = unsafe { FlattenedDeviceTree::from_raw_pointer(flattened_device_tree_address)? };

    // TODO: make sure the system has enough physical memory
    debug!("init_security_monitor: Initializing memory layout...");
    let (confidential_memory_start, confidential_memory_end) = initialize_memory_layout(&fdt)?;

    // Creates page tokens, heap, page allocator
    debug!("init_security_monitor: Initializing security monitor state...");
    initalize_security_monitor_state(confidential_memory_start, confidential_memory_end)?;
    // From now on, we can use heap.

    // Make sure harts implement all required extension
    debug!("init_security_monitor: Verifying harts...");
    let number_of_harts = verify_harts(&fdt)?;

    // Prepares memory required to store physical harts states during context switches
    debug!("init_security_monitor: Preparing harts...");
    prepare_harts(number_of_harts)?;

    // TODO: lock access to attestation keys/seed/credentials.

    // If we reached this line, then the security monitor control data has been correctly initialized, attestation keys have been created,
    // access to attestation seed has been restricted.
    Ok(())
}

/// Parses the flattened device tree (FDT) and reads the number of physical harts in the system. It verifies that these
/// harts support extensions required by ACE. Error is returned if FDT is incorrectly structured or exist a hart that
/// does not support required extensions.
fn verify_harts(fdt: &FlattenedDeviceTree) -> Result<usize, Error> {
    // All harts in the system can run the security monitor and every hart must implement all required features
    fdt.harts().try_for_each(|ref hart| {
        let prop = hart.property_str(FDT_RISCV_ISA).ok_or(Error::FdtParsing()).unwrap_or("");
        debug!("verify_harts: Hart {}", prop);
        // HardwareSetup::check_isa_extensions(prop)
        Ok::<(), Error>(())
    })?;

    // // Enable support for extensions that are implemented by all harts
    // HardwareExtension::all().into_iter().for_each(|ext| {
    //     let is_extension_supported_by_all_harts = fdt.harts().all(|hart| {
    //         let prop = hart.property_str(FDT_RISCV_ISA).ok_or(Error::FdtParsing()).unwrap_or("");
    //         let extensions = &prop.split('_').collect::<Vec<&str>>();
    //         extensions[0].contains(&ext.code()) || extensions.contains(&ext.code())
    //     });
    //     if is_extension_supported_by_all_harts {
    //         debug!("Enabling support for extension: {:?}", ext);
    //         let _ = HardwareSetup::add_extension(ext);
    //     }
    // });

    // TODO: make sure there are enough PMPs
    debug!("verify_harts: found {} harts", fdt.harts().count());

    Ok(fdt.harts().count())
}

/// Reads the layout of physical memory from the flattened device tree (FDT), splitting it (logically) into confidential and
/// non-confidential memory region. The FDT content is trusted.
///
/// # Guarantees
///
/// The end of the confidential memory is not lower than the start of the confidential memory
fn initialize_memory_layout(fdt: &FlattenedDeviceTree) -> Result<(ConfidentialMemoryAddress, *const usize), Error> {
    // TODO: FDT may contain multiple regions. For now, we assume there is only one region in the FDT.
    // This assumption is fine for the emulated environment (QEMU).

    // Information read from FDT is trusted assuming we are executing as part of a measured and secure boot. So we trust that we read the
    // correct base and size of the memory.
    let fdt_memory_region = fdt.memory()?;
    // Safety: We own all the memory because we are early in the boot process and have full rights to split memory according to our needs.
    // Thus, it is fine to cast `usize` to `*mut usize`.
    let memory_start = fdt_memory_region.base as *mut usize;
    // In assembly that executed this initialization function splitted the memory into two regions where
    // the second region's size is equal or greater than the first ones.
    let memory_size: usize = fdt_memory_region.size.try_into().map_err(|_| Error::InvalidMemoryBoundary())?;
    let non_confidential_memory_size = memory_size / 2;
    let confidential_memory_size = non_confidential_memory_size;
    let memory_end = memory_start.wrapping_byte_add(memory_size) as *const usize;
    debug!("Memory 0x{:#?}-0x{:#?}", memory_start, memory_end);

    // First region of memory is defined as non-confidential memory
    let non_confidential_memory_start = memory_start;
    let non_confidential_memory_end = ptr_byte_add_mut(non_confidential_memory_start, non_confidential_memory_size, memory_end)
        .map_err(|_| Error::InvalidMemoryBoundary())?;
    debug!("Non-confidential memory 0x{:#?}-0x{:#?}", non_confidential_memory_start, non_confidential_memory_end);

    // Second region of memory is defined as confidential memory
    let confidential_memory_start = non_confidential_memory_end;
    debug!("Confidential memory start: 0x{:#?}", confidential_memory_start);
    debug!("Confidential memory size: 0x{:x}", confidential_memory_size);
    ensure!(confidential_memory_start.is_aligned_to(PageSize::smallest().in_bytes()), Error::InvalidMemoryBoundary())?;
    debug!("Confidential memory size: 0x{:x}", confidential_memory_size);
    let confidential_memory_end = memory_end; // fixed bug with pointer arithmetic
    debug!("Confidential memory 0x{:#?}-0x{:#?}", confidential_memory_start, confidential_memory_end);

    unsafe {
        MemoryLayout::init(non_confidential_memory_start, non_confidential_memory_end, confidential_memory_start, confidential_memory_end)
    }
}

/// This function is called only once during the initialization of the security
/// monitor during the boot process. This function initializes secure monitor's
/// memory management like allocators.
fn initalize_security_monitor_state(
    confidential_memory_start: ConfidentialMemoryAddress, confidential_memory_end: *const usize,
) -> Result<(), Error> {
    // Safety: initialization order is crucial for safety because at some point we
    // start allocating objects on heap, e.g., page tokens. We have to first
    // initialize the global allocator, which permits us to use heap. To initialize heap
    // we need to decide what is the confidential memory address range and split this memory
    // into regions owned by heap allocator and page allocator.
    let confidential_memory_size = confidential_memory_start.offset_from(confidential_memory_end);
    assert!(confidential_memory_size > 0);

    let number_of_pages = confidential_memory_size as usize / PageSize::smallest().in_bytes();
    debug!("initalize_security_monitor_state: number of pages {}", number_of_pages);
    // Calculate if we have enough memory in the system to store page tokens. In the worst case we
    // have one page token for every possible page in the confidential memory.
    let size_of_a_page_token_in_bytes = size_of::<Page<UnAllocated>>();
    let bytes_required_to_store_page_tokens = number_of_pages * size_of_a_page_token_in_bytes;
    let heap_pages = NUMBER_OF_HEAP_PAGES + (bytes_required_to_store_page_tokens / PageSize::smallest().in_bytes());
    debug!("initalize_security_monitor_state: number of heap pages {}", heap_pages);
    ensure!(number_of_pages > heap_pages, Error::NotEnoughMemory())?;
    // Set up the global allocator so we can start using alloc::*.
    let heap_size_in_bytes = heap_pages * PageSize::smallest().in_bytes();
    let mut heap_start_address = confidential_memory_start;
    let heap_end_address = MemoryLayout::read().confidential_address_at_offset(&mut heap_start_address, heap_size_in_bytes)?;
    debug!("initalize_security_monitor_state: initializing heap...");
    crate::core::heap_allocator::init_heap(heap_start_address, heap_size_in_bytes);

    // PageAllocator's memory starts directly after the HeapAllocator's memory
    let page_allocator_start_address = heap_end_address;
    assert!(page_allocator_start_address.is_aligned_to(PageSize::smallest().in_bytes()));
    // PageAllocator takes ownership of the rest of the confidential memory.
    let page_allocator_end_address = confidential_memory_end;
    // It is safe to construct the PageAllocator because we own the corresponding memory region and pass this
    // ownership to the PageAllocator.
    debug!("initalize_security_monitor_state: initializing page allocator...");
    unsafe { PageAllocator::initialize(page_allocator_start_address, page_allocator_end_address)? };

    debug!("initalize_security_monitor_state: initializing interrupt controller...");
    InterruptController::initialize()?;
    debug!("initalize_security_monitor_state: initializing control data storage...");
    ControlDataStorage::initialize()?;
    debug!("initalize_security_monitor_state: initializing hardware setup...");
    HardwareSetup::initialize()?;

    Ok(())
}

fn prepare_harts(number_of_harts: usize) -> Result<(), Error> {
    // We need to allocate stack for the dumped state of each physical hart.
    debug!("initalize_security_monitor_state: initializing per-hart stack...");
    let mut harts_states = Vec::with_capacity(number_of_harts);
    for hart_id in 0..number_of_harts {
        let stack = PageAllocator::acquire_page(PageSize::Size2MiB)?;
        let hypervisor_memory_protector = HypervisorMemoryProtector::create();
        debug!("Hart[{}] stack \t 0x{:x}-0x{:x}", hart_id, stack.start_address(), stack.end_address());
        harts_states.insert(hart_id, HardwareHart::init(hart_id, stack, hypervisor_memory_protector));
    }
    debug!("initalize_security_monitor_state: initializing per-hart mutex...");
    HARTS_STATES.call_once(|| Mutex::new(harts_states));
    fence_wo();
    debug!("initalize_security_monitor_state: harts initialized");
    Ok(())
}

/// Enables entry points to the security monitor by taking control over some interrupts and protecting confidential
/// memory region using hardware isolation mechanisms. This function executes on every single physical hart.
#[no_mangle]
extern "C" fn ace_setup_this_hart() {
    // wait until the boot hart initializes the security monitor's data structures
    debug!("ace_setup_this_hart: configuring individual hart [before barrier]...");
    while !HARTS_STATES.is_completed() {
        fence_wo();
    }
    debug!("ace_setup_this_hart: configuring individual hart [after barrier]...");

    let hart_id = CSR.mhartid.read();
    debug!("Setting up hardware hart id={}", hart_id);

    // OpenSBI requires that mscratch points to an internal OpenSBI's structure. We have to store this pointer during
    // init and restore it every time we delegate exception/interrupt to the Sbi firmware (e.g., OpenSbi).
    let mut harts = HARTS_STATES.get().expect("Bug. Could not set mscratch before initializing memory region for harts states").lock();
    let hart = harts.get_mut(hart_id).expect("Bug. Incorrectly setup memory region for harts states");

    // The mscratch must point to the memory region when the security monitor stores the dumped states of
    // confidential harts. This is crucial for context switches because assembly code will use the mscratch
    // register to decide where to store/load registers content. Below 'swap' stores pointer to
    // opensbi_mscratch in the internal hart state. OpenSBI stored in mscratch a pointer to the
    // `opensbi_mscratch` region of this hart before calling the security monitor's initialization
    // procedure. Thus, the swap will move the mscratch register value into the dump state of the hart
    debug!("ace_setup_this_hart: swapping mscratch...");
    let hart_address = hart.hypervisor_hart().address();
    hart.set_ace_mscratch(hart_address);
    debug!("Hardware hart id={} has state area region at {:x}", hart_id, hart_address);

    // // Configure the memory isolation mechanism that can limit memory view of the hypervisor to the memory region
    // // owned by the hypervisor. The setup method enables the memory isolation. It is safe to call it because
    // // the `MemoryLayout` has been already initialized by the boot hart.
    debug!("ace_setup_this_hart: setting up memory protection...");
    if let Err(error) = unsafe { HypervisorMemoryProtector::setup() } {
        debug!("Failed to setup hypervisor memory protector: {:?}", error);
        // TODO: block access to attestation keys/registers on this hart?
        return;
    }
    debug!("ace_setup_this_hart: memory protection set up successfully...");

    // // Set up the trap vector, so that the exceptions are handled by the security monitor.
    let trap_vector_address = enter_from_hypervisor_or_vm_asm as usize;
    debug!(
        "Hardware hart id={} registered trap handler at address: {:x} (previous={:x})",
        hart_id,
        trap_vector_address,
        hart.hypervisor_hart_mut().csrs_mut().mtvec.read()
    );
    hart.hypervisor_hart_mut().csrs_mut().mtvec.write((trap_vector_address >> MTVEC_BASE_SHIFT) << MTVEC_BASE_SHIFT);
    debug!("ace_setup_this_hart: finished, going back to OpenSBI, mscratch={:x}", hart.hypervisor_hart().csrs().mscratch.read());
}
