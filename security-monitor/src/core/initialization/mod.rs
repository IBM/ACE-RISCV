// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ControlData, HardwareHart, CONTROL_DATA};
use crate::core::memory_tracker::{MemoryTracker, Page, UnAllocated, CONFIDENTIAL_MEMORY_RANGE, MEMORY_TRACKER};
use crate::core::mmu::PageSize;
use crate::error::{Error, InitializationErrorType, NOT_INITIALIZED_HART, NOT_INITIALIZED_HARTS};
use alloc::vec::Vec;
use core::ffi::c_void;
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
// the address of the memry region storing the corresponding hart state.
static HARTS_STATES: Once<Mutex<Vec<HardwareHart>>> = Once::new();

/// This is the entry point to the security monitor. It is called
/// by the OpenSBI during the boot process. After return, the control
/// flow returns to the OpenSBI that continues booting the hypervisor
#[no_mangle]
extern "C" fn init_security_monitor(fdt: *const c_void) {
    // Safety: initialization order is crucial for safety. We have to first
    // initialize the global allocator which then permits us to use the heap.
    debug!("initializing");

    // TODO: verify that the platform supports extensions we need (e.g., HS mode)
    // has enough memory, PMPs, IOPMP, etc.
    let number_of_harts = match read_number_of_cpus(fdt) {
        Ok(v) => v,
        Err(error) => {
            debug!("Failed while parsing FDT for CPUs: {:?}", error);
            return;
        }
    };

    let (base_address, end_address) = match read_memory_region(fdt) {
        Ok(v) => v,
        Err(error) => {
            debug!("Failed while parsing FDT: {:?}", error);
            return;
        }
    };

    // Isolate confidential memory using PMP and IOPMP
    configure_pmps(base_address, end_address);

    configure_iopmps();

    if let Err(error) = init_confidential_memory(base_address, end_address, number_of_harts) {
        debug!("Could not create confidential memory: {:?}", error);
        return;
    }

    if let Err(error) = set_delegation() {
        debug!("Could not change the interrupt/exception delegation: {:?}", error);
        return;
    }

    // if we reached this line, then the security monitor has been correctly
    // initialized. This means that we can safely generate attestation keys
}

fn read_number_of_cpus(_fdt: *const c_void) -> Result<usize, Error> {
    debug!("Number of harts: {}", 0);
    // debug!("RISC-V ISA: {}", "");
    // debug!("MMU system: {}", "");

    Ok(8)
}

fn read_memory_region(fdt: *const c_void) -> Result<(usize, usize), Error> {
    use fdt_rs::base::DevTree;
    use fdt_rs::prelude::{FallibleIterator, PropReader};

    // TODO: FDT may contain multiple regions. For now, we assume there is only one
    // This assumption is fine for the emulated environment (QEMU).

    // Safety: This unsafe is fine because we trust that the boot loader gave us a
    // correct address of a flatten device tree.
    let blob = unsafe { DevTree::from_raw_pointer(fdt as *const u8)? };
    let mem_prop = blob
        .props()
        .find(|p| Ok(p.name()? == "device_type" && p.str()? == "memory"))?
        .ok_or_else(|| Error::InitializationError(InitializationErrorType::FdtMemory))?;
    let mem_node = mem_prop.node();

    let reg_prop = mem_node
        .props()
        .find(|p| Ok(p.name().unwrap_or("empty") == "reg"))?
        .ok_or_else(|| Error::InitializationError(InitializationErrorType::FdtMemoryReg))?;
    let base = reg_prop.u64(0)?;
    let size = reg_prop.u64(1)?;

    // assume here that the memory has been already split in two chunks during early
    // execution of the OpenSBI code
    let confidential_memory_base_address: usize =
        (base + size).try_into().map_err(|_| Error::InitializationError(InitializationErrorType::FdtMemoryCasting))?;
    let confidential_memory_size: usize =
        size.try_into().map_err(|_| Error::InitializationError(InitializationErrorType::FdtMemoryCasting))?;
    let confidential_memory_end_address: usize = (confidential_memory_base_address + confidential_memory_size)
        .try_into()
        .map_err(|_| Error::InitializationError(InitializationErrorType::FdtMemoryCasting))?;

    debug!("Non-confidential memory {:X}-{:X}", base, base + size);
    debug!("Confidential memory {:X}-{:X}", confidential_memory_base_address, confidential_memory_end_address);

    if confidential_memory_end_address <= confidential_memory_base_address {
        return Err(Error::InitializationError(InitializationErrorType::InvalidMemoryBoundaries));
    }

    Ok((confidential_memory_base_address, confidential_memory_end_address))
}

fn configure_iopmps() {
    debug!("TODO: implement IOPMP setup");
}

/// This function is called only once during the initialization of the security
/// monitor during the boot process. This function initializes secure monitor's
/// memory management like allocators.
fn init_confidential_memory(mut start_address: usize, end_address: usize, number_of_harts: usize) -> Result<(), Error> {
    // align to 4KiB.
    // TODO: to what page size should we align to???
    let mut start_address_aligned =
        (start_address + PageSize::Size4KiB.in_bytes() - 1) & !(PageSize::Size4KiB.in_bytes() - 1);
    if start_address_aligned < start_address {
        start_address_aligned =
            (start_address + 2 * PageSize::Size4KiB.in_bytes() - 1) & !(PageSize::Size4KiB.in_bytes() - 1);
    }
    start_address = start_address_aligned;

    // calculate if we have enough memory in the system
    let memory_size = end_address - start_address;
    let available_pages = memory_size / PageSize::Size4KiB.in_bytes();
    let minimum_memory_tracker_size = available_pages * core::mem::size_of::<Page<UnAllocated>>();
    let minimum_pages = 4 * 1024 + (minimum_memory_tracker_size / PageSize::Size4KiB.in_bytes());
    if available_pages < minimum_pages {
        return Err(Error::InitializationError(InitializationErrorType::NotEnoughMemory));
    }

    // Set up the global allocator so we can start using alloc::*.
    let heap_pages = minimum_pages;
    let heap_size = heap_pages * PageSize::Size4KiB.in_bytes();
    crate::core::heap::init_heap(start_address, heap_size);

    // Memory tracker takes control over all confidential memory except for the
    // initial pages that it occupies
    let tracker_memory_start = start_address + heap_size;
    let tracker_memory_size = PageSize::Size4KiB.in_bytes() * (available_pages - heap_pages);
    debug!("Memory tracker {:x}-{:x}", tracker_memory_start, tracker_memory_start + tracker_memory_size);
    let memory_tracker = MemoryTracker::new(tracker_memory_start, tracker_memory_size)?;
    MEMORY_TRACKER.call_once(|| RwLock::new(memory_tracker));
    CONFIDENTIAL_MEMORY_RANGE.call_once(|| start_address..end_address);

    // we need to allocate stack for the dumped state of each physical HART.
    let mut physical_harts_states = Vec::with_capacity(number_of_harts);
    for hart_id in 0..number_of_harts {
        let stack = MemoryTracker::acquire_continous_pages(1, PageSize::Size2MiB)?.remove(0);
        debug!(
            "Init area for HART[{}], stack {:x}-{:x}",
            hart_id,
            stack.address().usize(),
            stack.end_address().usize()
        );
        physical_harts_states.insert(hart_id, HardwareHart::init(hart_id, stack));
    }
    CONTROL_DATA.call_once(|| RwLock::new(ControlData::new()));
    HARTS_STATES.call_once(|| Mutex::new(physical_harts_states));

    Ok(())
}

// OpenSBI set already PMPs to isolate OpenSBI firmware from the rest of the
// system PMP0 protects OpenSBI memory region while PMP1 defines the system
// range We will use PMP0 and PMP1 to protect the confidential memory region,
// PMP2 to protect the OpenSBI, and PMP3 to define the system range.
fn configure_pmps(confidential_memory_base_address: usize, confidential_memory_end_address: usize) {
    use riscv::register::{Permission, Range};
    const PMP_SHIFT: u16 = 2;

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
        riscv::register::pmpaddr0::write(confidential_memory_base_address >> PMP_SHIFT);
        riscv::register::pmpcfg0::set_pmp(0, Range::OFF, Permission::NONE, false);

        riscv::register::pmpaddr1::write(confidential_memory_end_address >> PMP_SHIFT);
        riscv::register::pmpcfg0::set_pmp(1, Range::TOR, Permission::NONE, false);
        riscv::asm::sfence_vma_all();
    }

    crate::debug::__print_pmp_configuration();
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
        .map_err(|_| Error::InitializationError(InitializationErrorType::InvalidAssemblyAddress))?;
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
