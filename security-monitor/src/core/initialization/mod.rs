// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ControlData, HardwareHart, CONTROL_DATA};
use crate::core::memory_tracker::{MemoryTracker, Page, UnAllocated, CONFIDENTIAL_MEMORY_RANGE, MEMORY_TRACKER};
use crate::core::mmu::PageSize;
use crate::error::{Error, HardwareFeatures, InitType, NOT_INITIALIZED_HART, NOT_INITIALIZED_HARTS};
use alloc::vec::Vec;
use core::mem::size_of;
use fdt::Fdt;
use pointers_utility::{ptr_align, ptr_byte_add_mut, ptr_byte_offset};
use spin::{Mutex, Once, RwLock};

extern "C" {
    fn enter_from_hypervisor_or_vm_asm() -> !;
}

// A *private* static array of hart states stores the hypervisor's harts states.
// Safe rust code cannot access this structure. We store the memory addresses
// of individual HardwareHart structure in the mscratch register. Thus, the
// assembly code of the context switch can store and load data from this data
// structure.
// Initialization procedure must guarantee that the mscratch register contains
// the address of the memory region that stores the state of the executing hart.
static HARTS_STATES: Once<Mutex<Vec<HardwareHart>>> = Once::new();

/// This is the entry point to the security monitor. It is called
/// by the OpenSBI during the boot process. After the return, the control
/// flow returns to the OpenSBI, which continues booting the hypervisor.
#[no_mangle]
extern "C" fn init_security_monitor_asm(flattened_device_tree_address: *const u8) {
    debug!("initializing the ACE extension");
    if let Err(error) = init_security_monitor(flattened_device_tree_address) {
        debug!("Failed to initialize the ACE extension: {:?}", error);
    }
}

fn init_security_monitor(flattened_device_tree_address: *const u8) -> Result<(), Error> {
    // Safety: pointer to the flattened device tree is trusted.
    let fdt = unsafe { Fdt::from_ptr(flattened_device_tree_address)? };

    let number_of_harts = read_number_of_cpus(&fdt)?;

    // TODO: make sure the system has enough physical memory
    let (confidential_memory_base_address, confidential_memory_end_address) = read_memory_region(&fdt)?;

    // Isolate the confidential memory region using PMP and IOPMP
    configure_pmps(confidential_memory_base_address, confidential_memory_end_address)?;
    configure_iopmps();

    // Create page tokens, heap,
    init_confidential_memory(confidential_memory_base_address, confidential_memory_end_address, number_of_harts)?;

    set_delegation()?;

    // if we reached this line, then the security monitor has been correctly
    // initialized. This means that we can generate attestation keys

    Ok(())
}

fn read_number_of_cpus(fdt: &Fdt) -> Result<usize, Error> {
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

fn read_memory_region(fdt: &Fdt) -> Result<(*mut usize, *const usize), Error> {
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

    Ok((confidential_memory_start, confidential_memory_end))
}

fn configure_iopmps() {
    debug!("TODO: implement IOPMP setup");
}

/// This function is called only once during the initialization of the security
/// monitor during the boot process. This function initializes secure monitor's
/// memory management like allocators.
fn init_confidential_memory(
    start_address: *mut usize, mut end_address: *const usize, number_of_harts: usize,
) -> Result<(), Error> {
    const NUMBER_OF_HEAP_PAGES: usize = 4 * 1024;
    // Safety: initialization order is crucial for safety because at some point we
    // start allocating objects on heap, e.g., page tokens. We have to first
    // initialize the global allocator, which permits us to use heap. To initialize heap
    // we need to decide what is the confidential memory address range and split this memory
    // into regions owned by heap allocator and page allocator (memory tracker).

    // We align the start of the confidential memory to the smalles possible page size (4KiB on RISC-V)
    // and make sure that its size is the multiply of this page size.
    let start_address = ptr_align(start_address, PageSize::smallest().in_bytes(), end_address)
        .map_err(|_| Error::Init(InitType::NotEnoughMemory))?;
    // Let's make sure that the end of the confidential memory is properly aligned.
    let memory_size = ptr_byte_offset(end_address, start_address);
    let memory_size = usize::try_from(memory_size).map_err(|_| Error::Init(InitType::NotEnoughMemory))?;
    let number_of_pages = memory_size / PageSize::smallest().in_bytes();
    let memory_size_in_bytes = number_of_pages * PageSize::smallest().in_bytes();
    if memory_size > memory_size_in_bytes {
        // we must modify the end_address because the current one is not a multiply of smalles page size
        end_address = ptr_byte_add_mut(start_address, memory_size_in_bytes, end_address)?;
    }
    // calculate if we have enough memory in the system to store page tokens. In the worst case we
    // have one page token for every possible page in the confidential memory.
    let size_of_a_page_token = size_of::<Page<UnAllocated>>();
    let number_of_pages_to_store_page_tokens = number_of_pages * size_of_a_page_token;
    let heap_pages = NUMBER_OF_HEAP_PAGES + (number_of_pages_to_store_page_tokens / PageSize::smallest().in_bytes());
    assure!(number_of_pages > heap_pages, Error::Init(InitType::NotEnoughMemory))?;
    // Set up the global allocator so we can start using alloc::*.
    let heap_size_in_bytes = heap_pages * PageSize::smallest().in_bytes();
    crate::core::heap::init_heap(start_address, heap_size_in_bytes);

    // Memory tracker starts directly after the heap
    let heap_end_address = ptr_byte_add_mut(start_address, heap_size_in_bytes, end_address)?;
    let memory_tracker_start_address = heap_end_address;
    assert!(memory_tracker_start_address.is_aligned_to(PageSize::smallest().in_bytes()));
    // Memory tracker takes ownership of the rest of the confidential memory.
    let memory_tracker_end_address = end_address;
    let memory_tracker = MemoryTracker::new(memory_tracker_start_address, memory_tracker_end_address)?;
    MEMORY_TRACKER.call_once(|| RwLock::new(memory_tracker));
    CONFIDENTIAL_MEMORY_RANGE.call_once(|| (start_address as usize)..(end_address as usize));

    // we need to allocate stack for the dumped state of each physical HART.
    let mut harts_states = Vec::with_capacity(number_of_harts);
    for hart_id in 0..number_of_harts {
        let stack = MemoryTracker::acquire_continous_pages(1, PageSize::Size2MiB)?.remove(0);
        debug!("HART[{}] stack {:x}-{:x}", hart_id, stack.start_address(), stack.end_address());
        harts_states.insert(hart_id, HardwareHart::init(hart_id, stack));
    }
    CONTROL_DATA.call_once(|| RwLock::new(ControlData::new()));
    HARTS_STATES.call_once(|| Mutex::new(harts_states));

    Ok(())
}

// OpenSBI set already PMPs to isolate OpenSBI firmware from the rest of the
// system PMP0 protects OpenSBI memory region while PMP1 defines the system
// range We will use PMP0 and PMP1 to protect the confidential memory region,
// PMP2 to protect the OpenSBI, and PMP3 to define the system range.
fn configure_pmps(
    confidential_memory_base_address: *const usize, confidential_memory_end_address: *const usize,
) -> Result<(), Error> {
    use riscv::register::{Permission, Range};
    const MINIMUM_NUMBER_OF_PMP_REQUIRED: usize = 4;
    const PMP_SHIFT: u16 = 2;

    // TODO: read how many PMPs are supported
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
        riscv::register::pmpaddr0::write(confidential_memory_base_address as usize >> PMP_SHIFT);
        riscv::register::pmpcfg0::set_pmp(0, Range::OFF, Permission::NONE, false);

        riscv::register::pmpaddr1::write(confidential_memory_end_address as usize >> PMP_SHIFT);
        riscv::register::pmpcfg0::set_pmp(1, Range::TOR, Permission::NONE, false);
        riscv::asm::sfence_vma_all();
    }

    crate::debug::__print_pmp_configuration();

    Ok(())
}

fn set_delegation() -> Result<(), Error> {
    // let the hypervisor handle all traps except for two exceptions
    // that carry potentially SM-calls. These exceptions will be trapped in the
    // security monitor. The security monitor trap handler will delegate these
    // calls to OpenSBI in case they are not directed for SM, or will process
    // them otherwise.
    unsafe {
        riscv::register::medeleg::clear_supervisor_env_call();
        riscv::register::medeleg::clear_virtual_supervisor_env_call();
    }

    // set up the trap vector, so the above exceptions are handled by the security
    //monitor.
    let trap_vector_address = (enter_from_hypervisor_or_vm_asm as usize)
        .try_into()
        .map_err(|_| Error::Init(InitType::InvalidAssemblyAddress))?;
    debug!("trap handler address: {:x}", trap_vector_address);
    unsafe {
        riscv::register::mtvec::write(trap_vector_address, riscv::register::mtvec::TrapMode::Direct);
    }

    // OpenSBI requires that mscratch points to an internal OpenSBI's structure we have to store this pointer during
    // init and restore it every time we will delegate exception/interrupt to the opensbi.
    let mut harts = HARTS_STATES.get().expect(NOT_INITIALIZED_HARTS).lock();
    let hart_id = riscv::register::mhartid::read();
    let hart = harts.get_mut(hart_id).expect(NOT_INITIALIZED_HART);

    // The mscratch must point to the memory region when the security monitor stores
    // the confidential_harts states. This is crucial for context switching because assembly
    // code will use the mscratch register to decide where to store/load registers
    // content.
    hart.swap_mscratch(); // this will store opensbi_mscratch in the internal hart state
    riscv::register::mscratch::write(hart.address());

    Ok(())
}
