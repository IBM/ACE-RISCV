// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::sbi::NaclSharedMemory;
use crate::core::architecture::riscv::specification::*;
use crate::core::architecture::{
    ControlStatusRegisters, GeneralPurposeRegister, GeneralPurposeRegisters, HardwareExtension, HartArchitecturalState, HartLifecycleState,
    SupervisorTimerExtension,
};
use crate::core::control_data::confidential_hart_remote_command::ConfidentialHartRemoteCommandExecutable;
use crate::core::control_data::{ConfidentialHartRemoteCommand, ConfidentialVmId, MeasurementDigest, ResumableOperation};
use crate::core::hardware_setup::HardwareSetup;
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::error::Error;

unsafe extern "C" {
    // Assembly function that is an entry point to the security monitor from the hypervisor or a virtual machine.
    fn enter_from_confidential_hart_asm();
}

/// ConfidentialHart represents the dump state of the confidential VM's hart (aka vcpu). The only publicly exposed way
/// to modify the confidential hart architectural state (registers/CSRs) is by calling the constructor or applying a
/// transformation.
#[repr(C)]
pub struct ConfidentialHart {
    // Safety: HardwareHart and ConfidentialHart must both start with the HartArchitecturalState element
    // because based on this we automatically calculate offsets of registers' and CSRs' for the asm code.
    confidential_hart_state: HartArchitecturalState,
    /// Unique identifier of the confidential hart.
    id: usize,
    // If there is no confidential vm id assigned to this hart then it means that this confidential hart is a dummy
    // one. A dummy virtual hart means that the confidential_hart is not associated with any confidential VM but is
    // used to prevent some concurrency issues like attempts of assigning the same confidential hart to many physical
    // cores.
    confidential_vm_id: Option<ConfidentialVmId>,
    /// The confidential hart's lifecycle follow the finite state machine (FSM) of a hart defined in SBI HSM extension.
    lifecycle_state: HartLifecycleState,
    /// A pending request indicates that the confidential hart sent a request to the hypervisor and is waiting for its
    /// reply. The pending request defines the expected response.
    resumable_operation: Option<ResumableOperation>,
}

impl ConfidentialHart {
    /// Configuration of RISC-V exceptions for confidential hart
    const EXCEPTION_DELEGATION: usize = (1 << CAUSE_MISALIGNED_FETCH)
        | (1 << CAUSE_FETCH_ACCESS)
        | (1 << CAUSE_ILLEGAL_INSTRUCTION)
        | (1 << CAUSE_BREAKPOINT)
        | (1 << CAUSE_MISALIGNED_LOAD)
        | (1 << CAUSE_LOAD_ACCESS)
        | (1 << CAUSE_MISALIGNED_STORE)
        | (1 << CAUSE_STORE_ACCESS)
        | (1 << CAUSE_USER_ECALL)
        | (1 << CAUSE_FETCH_PAGE_FAULT)
        | (1 << CAUSE_LOAD_PAGE_FAULT)
        | (1 << CAUSE_STORE_PAGE_FAULT);
    const INITIAL_MSTATUS: usize =
        ((1 << CSR_MSTATUS_MPV) | (1 << CSR_MSTATUS_MPP) | (1 << CSR_MSTATUS_SIE) | (1 << CSR_MSTATUS_SPIE)) & !(1 << CSR_MSTATUS_MPIE);
    const INITIAL_HSTATUS: usize = (1 << CSR_HSTATUS_VTW) | (1 << CSR_HSTATUS_SPVP) | (1 << CSR_HSTATUS_UXL);
    const INITIAL_SSTATUS: usize = (1 << CSR_SSTATUS_SPIE) | (1 << CSR_SSTATUS_UXL);
    /// Configuration of delegation of RISC-V interrupts that will trap directly in the confidential hart. All other interrupts will trap in
    /// the security monitor.
    const INTERRUPT_DELEGATION: usize = MIE_VSSIP_MASK | MIE_VSTIP_MASK | MIE_VSEIP_MASK;
    const ENABLED_INTERRUPTS: usize = Self::INTERRUPT_DELEGATION | MIE_STIP_MASK | MIE_MEIP_MASK | MIE_MSIP_MASK | MIE_MTIP_MASK;

    /// Constructs a dummy hart. This dummy hart carries no confidential information. It is used to indicate that a real
    /// confidential hart has been assigned to a hardware hart for execution. A dummy confidential hart has the id of the hardware hart it
    /// represents. This is required to track information on which hardware hart a stolen confidential hart executes (for example to
    /// interrupt it with IPI).
    pub fn dummy(hardware_hart_id: usize) -> Self {
        // We set the lifecycle state of the dummy hart to `Started` because this state will be used as the state of the confidential hart
        // that has been assigned to physical hart. Specifically, after a confidential hart gets assigned to hardware hart, the confidential
        // VM will be left with a dummy hart. Any other code or request that will inspect the state of the (stolen) confidential hart, will
        // in reality look into the state of the dummy hart which will correctly say that the confidential hart is in the `Started` state.
        Self {
            confidential_vm_id: None,
            confidential_hart_state: HartArchitecturalState::empty(),
            lifecycle_state: HartLifecycleState::Started,
            resumable_operation: None,
            id: hardware_hart_id,
        }
    }

    /// Constructs a confidential hart with the state after a reset.
    pub fn from_vm_hart_reset(id: usize, htimedelta: usize, shared_memory: &NaclSharedMemory) -> Self {
        let mut confidential_hart_state = HartArchitecturalState::empty();
        confidential_hart_state.csrs_mut().mstatus.save_value_in_main_memory(Self::INITIAL_MSTATUS);
        confidential_hart_state.csrs_mut().sstatus.save_value_in_main_memory(Self::INITIAL_SSTATUS);
        confidential_hart_state.csrs_mut().hstatus.save_value_in_main_memory(Self::INITIAL_HSTATUS);
        confidential_hart_state.csrs_mut().medeleg.save_value_in_main_memory(Self::EXCEPTION_DELEGATION);
        confidential_hart_state.csrs_mut().hedeleg.save_value_in_main_memory(Self::EXCEPTION_DELEGATION);
        confidential_hart_state.csrs_mut().mideleg.save_value_in_main_memory(Self::INTERRUPT_DELEGATION);
        confidential_hart_state.csrs_mut().hideleg.save_value_in_main_memory(Self::INTERRUPT_DELEGATION);
        // the `vsie` register reflects `hie`, so we set up `hie` allowing only VS-level interrupts
        confidential_hart_state.csrs_mut().hie.save_value_in_main_memory(Self::ENABLED_INTERRUPTS);
        // Allow only hypervisor's timer interrupts to preemt confidential VM's execution
        confidential_hart_state.csrs_mut().mie.save_value_in_main_memory(Self::ENABLED_INTERRUPTS);
        confidential_hart_state.csrs_mut().htimedelta.save_value_in_main_memory(htimedelta);
        // Setup the M-mode trap handler to the security monitor's entry point
        confidential_hart_state.csrs_mut().mtvec.save_value_in_main_memory(enter_from_confidential_hart_asm as usize);

        // There is a subset of S-mode CSRs that have no VS equivalent and preserve their function when virtualization is enabled (see
        // `Hypervisor and Virtual Supervisor CSRs` in Volume II: RISC-V Privileged Architectures V20211203).
        confidential_hart_state.csrs_mut().henvcfg.save_nacl_value_in_main_memory(shared_memory);
        let henvcfg = confidential_hart_state.csrs_mut().henvcfg.read_from_main_memory();
        confidential_hart_state.csrs_mut().senvcfg.save_value_in_main_memory(henvcfg);
        // Code running in VS-mode should directly access only the timer. Everything else must trap:
        confidential_hart_state.csrs_mut().hcounteren.save_value_in_main_memory(HCOUNTEREN_TM_MASK);
        confidential_hart_state.csrs_mut().scounteren.save_value_in_main_memory(HCOUNTEREN_TM_MASK);

        assert!(HardwareSetup::is_extension_supported(HardwareExtension::SupervisorTimerExtension));
        // Preempt execution as fast as possible to allow hypervisor control confidential hart execution duration
        confidential_hart_state.sstc_mut().stimecmp.save_value_in_main_memory(0);

        if HardwareSetup::is_extension_supported(HardwareExtension::FloatingPointExtension) {
            confidential_hart_state.csrs_mut().mstatus.enable_bits_on_saved_value(SR_FS_INITIAL);
        }

        Self {
            confidential_vm_id: None,
            confidential_hart_state,
            lifecycle_state: HartLifecycleState::Stopped,
            resumable_operation: None,
            id,
        }
    }

    /// Constructs a confidential hart with the state of the non-confidential hart that made a call to promote the VM to confidential VM
    pub fn from_vm_hart(
        id: usize, program_counter: usize, fdt_address: &ConfidentialVmPhysicalAddress, htimedelta: usize, shared_memory: &NaclSharedMemory,
    ) -> Self {
        // We first create a confidential hart in the reset state and then fill this state with the runtime state of the hart that made a
        // call to promote to confidential VM. This state consists of GPRs and VS-level CSRs.
        let mut confidential_hart = Self::from_vm_hart_reset(id, htimedelta, shared_memory);
        let confidential_hart_state = &mut confidential_hart.confidential_hart_state;
        confidential_hart_state.set_gprs(shared_memory.gprs());
        confidential_hart_state.gprs_mut().write(GeneralPurposeRegister::a0, id);
        confidential_hart_state.gprs_mut().write(GeneralPurposeRegister::a1, fdt_address.usize());
        confidential_hart_state.csrs_mut().vsstatus.save_nacl_value_in_main_memory(&shared_memory);
        confidential_hart_state.csrs_mut().vsie.save_nacl_value_in_main_memory(&shared_memory);
        confidential_hart_state.csrs_mut().vstvec.save_nacl_value_in_main_memory(&shared_memory);
        confidential_hart_state.csrs_mut().vsscratch.save_nacl_value_in_main_memory(&shared_memory);
        confidential_hart_state.csrs_mut().vsepc.save_nacl_value_in_main_memory(&shared_memory);
        confidential_hart_state.csrs_mut().vscause.save_nacl_value_in_main_memory(&shared_memory);
        confidential_hart_state.csrs_mut().vstval.save_nacl_value_in_main_memory(&shared_memory);
        confidential_hart_state.csrs_mut().vsatp.save_nacl_value_in_main_memory(&shared_memory);
        // Store the program counter of the VM, so that we can resume confidential VM at the point it became promoted.
        confidential_hart_state.csrs_mut().mepc.save_value_in_main_memory(program_counter);
        confidential_hart.lifecycle_state = HartLifecycleState::Started;
        confidential_hart
    }

    /// Saves the state of the confidential hart in the main memory. This is part of the heavy context switch.
    pub fn save_in_main_memory(&mut self) {
        self.csrs_mut().save_in_main_memory();
        // below unsafe is ok because we ensured during the initialization that Sstc extension is present.
        unsafe { self.sstc_mut().save_in_main_memory() };

        // If only hardware supports F extension, we must always switch its context.
        // One reason is time side channel (attacker can infer from the duration of the context switch whether the F registers were dirty
        // and thus were stored in the main memory). Other reason is that F registers are shared between different security domains.
        // Even if it looks like F extension is disabled, a security domain might enable it and then access F registers. We must
        // guarantee that these F registers do not disclose information from other security domains. The same is true for all other
        // extensions, e.g., V extension.
        if HardwareSetup::is_extension_supported(HardwareExtension::FloatingPointExtension) {
            // Enable F extension to access F registers. The lightweight context switch will eventually recover valid F configuration in
            // mstatus, so we do not have to set it back to the original value after this context switch.
            self.csrs().mstatus.read_and_set_bits(SR_FS);
            // below unsafe is ok because we checked that FPU hardware is available and we enabled it in mstatus.
            unsafe { self.confidential_hart_state.fprs_mut().save_in_main_memory() };
            self.csrs_mut().vsstatus.disable_bits_on_saved_value(SR_FS_DIRTY);
            self.csrs_mut().vsstatus.enable_bits_on_saved_value(SR_FS_CLEAN);
        }
    }

    /// Restores the state of the confidential hart from the main memory. This is part of the heavy context switch.
    pub fn restore_from_main_memory(&mut self) {
        self.csrs().restore_from_main_memory();
        // below unsafe is ok because we ensured during the initialization that Sstc extension is present.
        unsafe { self.sstc().restore_from_main_memory() };

        if HardwareSetup::is_extension_supported(HardwareExtension::FloatingPointExtension) {
            // Enable F extension to access F registers. The lightweight context switch will eventually recover the valid F configuration in
            // mstatus, so we do not have to set it back to the original value after this context switch.
            self.csrs().mstatus.read_and_set_bits(SR_FS);
            // below unsafe is ok because we checked that FPU hardware is available and we enabled it in mstatus.
            unsafe { self.confidential_hart_state.fprs_mut().restore_from_main_memory() };
        }
    }

    pub fn measure(&self, digest: &mut MeasurementDigest) {
        self.confidential_hart_state.gprs().measure(digest);
        self.confidential_hart_state.csrs().measure(digest);
    }

    pub fn address(&self) -> usize {
        core::ptr::addr_of!(self.confidential_hart_state) as usize
    }

    pub fn set_confidential_vm_id(&mut self, confidential_vm_id: ConfidentialVmId) {
        self.confidential_vm_id = Some(confidential_vm_id);
    }

    pub fn confidential_vm_id(&self) -> Option<ConfidentialVmId> {
        self.confidential_vm_id
    }

    pub fn confidential_hart_id(&self) -> usize {
        self.id
    }

    // Returns the id of the hardware hart executing the confidential hart.
    pub fn hardware_hart_id(&self) -> Option<usize> {
        self.confidential_vm_id.map_or_else(|| Some(self.id), |_| None)
    }

    pub fn gprs(&self) -> &GeneralPurposeRegisters {
        self.confidential_hart_state.gprs()
    }

    pub fn gprs_mut(&mut self) -> &mut GeneralPurposeRegisters {
        self.confidential_hart_state.gprs_mut()
    }

    pub fn csrs(&self) -> &ControlStatusRegisters {
        self.confidential_hart_state.csrs()
    }

    pub fn csrs_mut(&mut self) -> &mut ControlStatusRegisters {
        self.confidential_hart_state.csrs_mut()
    }

    pub fn sstc(&self) -> &SupervisorTimerExtension {
        self.confidential_hart_state.sstc()
    }

    pub fn sstc_mut(&mut self) -> &mut SupervisorTimerExtension {
        self.confidential_hart_state.sstc_mut()
    }

    pub fn confidential_hart_state(&self) -> &HartArchitecturalState {
        &self.confidential_hart_state
    }

    pub fn is_dummy(&self) -> bool {
        self.confidential_vm_id.is_none()
    }

    pub fn is_executable(&self) -> bool {
        HartLifecycleState::STATES_ALLOWED_TO_EXECUTE.contains(&self.lifecycle_state)
    }
}

// Methods related to resumable operation, i.e., requests from the confidential hart that must be served by the hypervisor and the result
// must be then declassified to the confidential hart.
impl ConfidentialHart {
    pub fn take_resumable_operation(&mut self) -> Option<ResumableOperation> {
        self.resumable_operation.take()
    }

    /// Stores a resumable operation inside the confidential hart's state. Before the next execution of this confidential
    /// hart, the security monitor will declassify a response to this request that should come from another security
    /// domain, like hypervisor.
    ///
    /// # Correctness of the confidential hart execution
    ///
    /// The confidential hart must not be associated with any resumable operation. Any resumable operation must be completed on resuming
    /// confidential hart's execution. Before exiting to the hypervisor, the security monitor can set up the resumable operation only once.
    pub fn set_resumable_operation(&mut self, request: ResumableOperation) {
        assert!(self.resumable_operation.is_none());
        self.resumable_operation = Some(request);
    }
}

// Methods related to lifecycle state transitions of the confidential hart. These methods manipulate the internal hart
// state in a response to requests from (1) the confidential hart itself (started->stop or started->suspend), from
// other confidential hart (stopped->started), or hypervisor (suspend->started). Check out the SBI' HSM extensions for
// more details.
impl ConfidentialHart {
    pub fn lifecycle_state(&self) -> &HartLifecycleState {
        if self.is_dummy() { &HartLifecycleState::Started } else { &self.lifecycle_state }
    }

    /// Changes the lifecycle state of the hart into the `StartPending` state. Confidential hart's state is set as if
    /// the hart was reset. This function is called as a response of another confidential hart (typically a boot hart)
    /// to start another confidential hart. Returns error if the confidential hart is not in stopped state.
    pub fn transition_from_stopped_to_started(&mut self, start_address: usize, opaque: usize) -> Result<(), Error> {
        ensure_not!(self.is_dummy(), Error::HartAlreadyRunning())?;
        ensure!(self.lifecycle_state == HartLifecycleState::Stopped, Error::CannotStartNotStoppedHart())?;
        // Let's set up the confidential hart initial state so that it can be run
        self.lifecycle_state = HartLifecycleState::Started;
        // Following the SBI documentation of the function `hart start` in the HSM extension, only vsatp, vsstatus.SIE,
        // a0, a1 have defined values, all other registers are in an undefined state. The hart will start
        // executing in the supervisor mode with disabled MMU (vsatp=0).
        self.confidential_hart_state.csrs_mut().vsatp.save_value_in_main_memory(0);
        // start the new confidential hart with interrupts disabled
        self.confidential_hart_state.csrs_mut().mstatus.disable_bit_on_saved_value(CSR_MSTATUS_SPIE);
        self.confidential_hart_state.csrs_mut().mstatus.disable_bit_on_saved_value(CSR_MSTATUS_MPIE);
        self.confidential_hart_state.csrs_mut().vsstatus.disable_bit_on_saved_value(CSR_STATUS_SIE);
        self.confidential_hart_state.gprs_mut().write(GeneralPurposeRegister::a0, self.id);
        self.confidential_hart_state.gprs_mut().write(GeneralPurposeRegister::a1, opaque);
        self.confidential_hart_state.csrs_mut().mepc.save_value_in_main_memory(start_address);
        Ok(())
    }

    pub fn transition_from_started_to_suspended(&mut self) -> Result<(), Error> {
        assert!(!self.is_dummy());
        ensure!(self.lifecycle_state == HartLifecycleState::Started, Error::CannotSuspedNotStartedHart())?;
        self.lifecycle_state = HartLifecycleState::Suspended;
        Ok(())
    }

    pub fn transition_from_started_to_stopped(&mut self) -> Result<(), Error> {
        assert!(!self.is_dummy());
        ensure!(self.lifecycle_state == HartLifecycleState::Started, Error::CannotStopNotStartedHart())?;
        self.lifecycle_state = HartLifecycleState::Stopped;
        Ok(())
    }

    pub fn transition_from_suspended_to_started(&mut self, start_address: usize, opaque: usize) -> Result<(), Error> {
        assert!(!self.is_dummy());
        ensure!(self.lifecycle_state == HartLifecycleState::Suspended, Error::CannotStartNotSuspendedHart())?;
        self.lifecycle_state = HartLifecycleState::Started;
        self.confidential_hart_state.gprs_mut().write(GeneralPurposeRegister::a1, opaque);
        self.confidential_hart_state.csrs_mut().mepc.save_value_in_main_memory(start_address);
        Ok(())
    }

    pub fn transition_to_shutdown(&mut self) {
        assert!(!self.is_dummy());
        self.lifecycle_state = HartLifecycleState::PoweredOff;
    }
}

impl ConfidentialHart {
    pub fn execute(&mut self, request: &ConfidentialHartRemoteCommand) {
        match request {
            ConfidentialHartRemoteCommand::Ipi(v) => v.execute_on_confidential_hart(self),
            ConfidentialHartRemoteCommand::RemoteFenceI(v) => v.execute_on_confidential_hart(self),
            ConfidentialHartRemoteCommand::RemoteSfenceVma(v) => v.execute_on_confidential_hart(self),
            ConfidentialHartRemoteCommand::RemoteSfenceVmaAsid(v) => v.execute_on_confidential_hart(self),
            ConfidentialHartRemoteCommand::RemoteHfenceGvmaVmid(v) => v.execute_on_confidential_hart(self),
            ConfidentialHartRemoteCommand::ShutdownRequest(_) => self.transition_to_shutdown(),
        }
    }
}
