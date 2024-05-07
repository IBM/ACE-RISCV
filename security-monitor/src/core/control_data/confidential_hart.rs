// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::smp::{SbiHsmHartStart, SbiHsmHartSuspend};
use crate::core::architecture::{GeneralPurposeRegister, HartArchitecturalState, HartLifecycleState, *};
use crate::core::control_data::inter_hart_request::InterHartRequestExecutable;
use crate::core::control_data::{ConfidentialVmId, InterHartRequest, PendingRequest};
use crate::error::Error;

extern "C" {
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
    // If there is no confidential vm id assigned to this hart then it means that this confidential hart is a dummy
    // one. A dummy virtual hart means that the confidential_hart is not associated with any confidential VM but is
    // used to prevent some concurrency issues like attempts of assigning the same confidential hart to many physical
    // cores.
    confidential_vm_id: Option<ConfidentialVmId>,
    /// The confidential hart's lifecycle follow the finite state machine (FSM) of a hart defined in SBI HSM extension.
    lifecycle_state: HartLifecycleState,
    /// A pending request indicates that the confidential hart sent a request to the hypervisor and is waiting for its
    /// reply. The pending request defines the expected response.
    pending_request: Option<PendingRequest>,
    id: usize,
}

impl ConfidentialHart {
    /// Constructs a dummy hart. This dummy hart carries no confidential information. It is used to indicate that a real
    /// confidential hart has been assigned to a hardware hart for execution.
    pub fn dummy() -> Self {
        // We set the lifecycle state of the dummy hart to `Started` because this state will be used as the state of the confidential hart
        // that has been assigned to physical hart. Specifically, after a confidential hart gets assigned to hardware hart, the confidential
        // VM will be left with a dummy hart. Any other code or request that will inspect the state of the (stolen) confidential hart, will
        // in reality look into the state of the dummy hart which will correctly say that the confidential hart is in the `Started` state.
        Self {
            confidential_vm_id: None,
            confidential_hart_state: HartArchitecturalState::empty(),
            lifecycle_state: HartLifecycleState::Started,
            pending_request: None,
            id: 0,
        }
    }

    /// Constructs a confidential hart with the state after a reset.
    pub fn from_vm_hart_reset(id: usize, shared_memory: &NaclSharedMemory) -> Self {
        let mut confidential_hart_state = HartArchitecturalState::empty();
        // Set up mstatus, so that the lightweight context switch changes to privileg mode to VS-mode when executing the confidential VM
        // (see Table 8.8 in Riscv privilege spec 20211203)
        confidential_hart_state.csrs_mut().mstatus.save();
        confidential_hart_state.csrs_mut().mstatus.enable_bit_on_saved_value(CSR_MSTATUS_MPV);
        confidential_hart_state.csrs_mut().mstatus.enable_bit_on_saved_value(CSR_MSTATUS_MPP);
        confidential_hart_state.csrs_mut().mstatus.enable_bit_on_saved_value(CSR_MSTATUS_SIE);
        confidential_hart_state.csrs_mut().mstatus.enable_bit_on_saved_value(CSR_MSTATUS_SPIE);
        confidential_hart_state.csrs_mut().mstatus.disable_bit_on_saved_value(CSR_MSTATUS_MPIE);
        // enable extensions if available
        confidential_hart_state.csrs_mut().mstatus.enable_bits_on_saved_value(SR_FS_INITIAL);
        // Set up `sstatus` and `hstatus` to well known default values
        confidential_hart_state.csrs_mut().sstatus.save_value((1 << CSR_SSTATUS_SPIE) | (1 << CSR_SSTATUS_UXL));
        confidential_hart_state.csrs_mut().hstatus.save_value((1 << CSR_HSTATUS_VTW) | (1 << CSR_HSTATUS_SPVP) | (1 << CSR_HSTATUS_UXL));
        // Delegate VS-level interrupts directly to the confidential VM. All other interrupts will trap in the security monitor.
        let interrupt_delegation = MIE_VSSIP_MASK | MIE_VSTIP_MASK | MIE_VSEIP_MASK;
        confidential_hart_state.csrs_mut().mideleg.save_value(interrupt_delegation);
        confidential_hart_state.csrs_mut().hideleg.save_value(interrupt_delegation);
        // the `vsie` register reflects `hie`, so we set up `hie` allowing only VS-level interrupts
        confidential_hart_state.csrs_mut().hie.save_value(interrupt_delegation);
        // Allow only hypervisor's timer interrupts to preemt confidential VM's execution
        confidential_hart_state.csrs_mut().mie.save_value(MIE_STIP_MASK);
        // Delegate exceptions that can be handled directly in the confidential VM
        let exception_delegation = (1 << CAUSE_MISALIGNED_FETCH)
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
        confidential_hart_state.csrs_mut().medeleg.save_value(exception_delegation);
        confidential_hart_state.csrs_mut().hedeleg.save_value(exception_delegation);
        // Setup the M-mode trap handler to the security monitor's entry point
        confidential_hart_state.csrs_mut().mtvec.save_value(enter_from_confidential_hart_asm as usize);
        // Set timer counter to infinity.
        let infinity = usize::MAX - 1;
        confidential_hart_state.csrs_mut().vstimecmp.save_value(infinity);
        confidential_hart_state.csrs_mut().stimecmp.save_value(infinity);
        // TODO: The same starting clock for all confidential harts within the same confidential VM.
        // TODO: generate our own value
        confidential_hart_state.csrs_mut().htimedelta.save();
        // There is a subset of S-mode CSRs that have no VS equivalent and preserve their function when virtualization is enabled (see
        // `Hypervisor and Virtual Supervisor CSRs` in Volume II: RISC-V Privileged Architectures V20211203)
        confidential_hart_state.csrs_mut().henvcfg.restore_from_nacl(shared_memory);
        confidential_hart_state.csrs_mut().senvcfg.save();
        // VS code should directly access only the timer. Everything else will trap
        confidential_hart_state.csrs_mut().hcounteren.save_value(0x02);
        confidential_hart_state.csrs_mut().scounteren.save();
        Self { confidential_vm_id: None, confidential_hart_state, lifecycle_state: HartLifecycleState::Stopped, pending_request: None, id }
    }

    /// Constructs a confidential hart with the state of the non-confidential hart that made a call to promote the VM to confidential VM
    pub fn from_vm_hart(id: usize, sepc: usize, shared_memory: &NaclSharedMemory) -> Self {
        // We first create a confidential hart in the reset state and then fill this state with the runtime state of the hart that made a
        // call to promote to confidential VM. This state consists of GPRs and VS-level CSRs.
        let mut confidential_hart = Self::from_vm_hart_reset(id, shared_memory);
        let confidential_hart_state = &mut confidential_hart.confidential_hart_state;
        confidential_hart_state.set_gprs(shared_memory.gprs());
        confidential_hart_state.csrs_mut().vsstatus.restore_from_nacl(&shared_memory);
        confidential_hart_state.csrs_mut().vsie.restore_from_nacl(&shared_memory);
        confidential_hart_state.csrs_mut().vstvec.restore_from_nacl(&shared_memory);
        confidential_hart_state.csrs_mut().vsscratch.restore_from_nacl(&shared_memory);
        confidential_hart_state.csrs_mut().vsepc.restore_from_nacl(&shared_memory);
        confidential_hart_state.csrs_mut().vscause.restore_from_nacl(&shared_memory);
        confidential_hart_state.csrs_mut().vstval.restore_from_nacl(&shared_memory);
        confidential_hart_state.csrs_mut().vsatp.restore_from_nacl(&shared_memory);
        // Store the program counter of the VM, so that we can resume confidential VM at the point it became promoted.
        confidential_hart_state.csrs_mut().mepc.save_value(sepc);
        confidential_hart.lifecycle_state = HartLifecycleState::Started;
        confidential_hart.pending_request = Some(PendingRequest::SbiRequest());
        confidential_hart
    }

    /// Saves the state of the confidential hart in the main memory. This is part of the heavy context switch.
    pub fn save_in_main_memory(&mut self) {
        self.csrs_mut().save_in_main_memory();
        if (self.csrs().vsstatus.read_value() & SR_FS_DIRTY) > 0 {
            self.csrs_mut().fflags.save();
            self.csrs_mut().frm.save();
            self.csrs_mut().fcsr.save();
            self.csrs_mut().vsstatus.disable_bits_on_saved_value(SR_FS_DIRTY);
            self.csrs_mut().vsstatus.enable_bits_on_saved_value(SR_FS_CLEAN);
            self.confidential_hart_state.fprs_mut().save_in_main_memory();
        }
    }

    /// Restores the state of the confidential hart from the main memory. This is part of the heavy context switch.
    pub fn restore_from_main_memory(&self) {
        self.csrs().restore_from_main_memory();
        // TODO: currently we might leak F state. Regardless of the configuration, we must always restore F state it, or zeroize it if the F
        // extension is disabled.
        if (self.csrs().mstatus.read() & SR_FS) > 0 {
            self.csrs().fflags.restore();
            self.csrs().frm.restore();
            self.csrs().fcsr.restore();
            self.confidential_hart_state.fprs().restore_from_main_memory();
        }
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

    pub fn confidential_hart_state(&self) -> &HartArchitecturalState {
        &self.confidential_hart_state
    }

    pub fn take_request(&mut self) -> Option<PendingRequest> {
        self.pending_request.take()
    }

    pub fn is_dummy(&self) -> bool {
        self.confidential_vm_id.is_none()
    }

    /// Returns true if this confidential hart can be scheduled on the physical hart.
    pub fn is_executable(&self) -> bool {
        let hart_states_allowed_to_resume = [HartLifecycleState::Started, HartLifecycleState::Suspended];
        !self.is_dummy() && hart_states_allowed_to_resume.contains(&self.lifecycle_state)
    }

    /// Stores a pending request inside the confidential hart's state. Before the next execution of this confidential
    /// hart, the security monitor will declassify a response to this request that should come from another security
    /// domain, like hypervisor.
    pub fn set_pending_request(&mut self, request: PendingRequest) -> Result<(), Error> {
        assure!(self.pending_request.is_none(), Error::PendingRequest())?;
        self.pending_request = Some(request);
        Ok(())
    }
}

// Methods related to lifecycle state transitions of the confidential hart. These methods manipulate the internal hart
// state in a response to requests from (1) the confidential hart itself (started->stop or started->suspend), from
// other confidential hart (stopped->started), or hypervisor (suspend->started). Check out the SBI' HSM extensions for
// more details.
impl ConfidentialHart {
    pub fn lifecycle_state(&self) -> &HartLifecycleState {
        &self.lifecycle_state
    }

    /// Changes the lifecycle state of the hart into the `StartPending` state. Confidential hart's state is set as if
    /// the hart was reset. This function is called as a response of another confidential hart (typically a boot hart)
    /// to start another confidential hart. Returns error if the confidential hart is not in stopped state.
    pub fn transition_from_stopped_to_started(&mut self, request: SbiHsmHartStart) -> Result<(), Error> {
        assure_not!(self.is_dummy(), Error::HartAlreadyRunning())?;
        assure!(self.lifecycle_state == HartLifecycleState::Stopped, Error::CannotStartNotStoppedHart())?;
        let confidential_hart_id = self.id;

        // Let's set up the confidential hart initial state so that it can be run
        self.lifecycle_state = HartLifecycleState::Started;

        // Following the SBI documentation of the function `hart start` in the HSM extension, only vsatp, vsstatus.SIE,
        // a0, a1 have defined values, all other registers are in an undefined state. The hart will start
        // executing in the supervisor mode with disabled MMU (vsatp=0).
        self.confidential_hart_state.csrs_mut().vsatp.save_value(0);
        // start the new confidential hart with interrupts disabled
        self.confidential_hart_state.csrs_mut().mstatus.disable_bit_on_saved_value(CSR_MSTATUS_SPIE);
        self.confidential_hart_state.csrs_mut().mstatus.disable_bit_on_saved_value(CSR_MSTATUS_MPIE);

        self.confidential_hart_state.csrs_mut().vsstatus.disable_bit_on_saved_value(CSR_STATUS_SIE);
        self.confidential_hart_state.gprs_mut().write(GeneralPurposeRegister::a0, confidential_hart_id);
        self.confidential_hart_state.gprs_mut().write(GeneralPurposeRegister::a1, request.opaque());
        self.confidential_hart_state.csrs_mut().mepc.save_value(request.start_address());
        Ok(())
    }

    pub fn transition_from_started_to_suspended(&mut self, _request: SbiHsmHartSuspend) -> Result<(), Error> {
        assert!(!self.is_dummy());
        assure!(self.lifecycle_state == HartLifecycleState::Started, Error::CannotSuspedNotStartedHart())?;
        self.lifecycle_state = HartLifecycleState::Suspended;
        Ok(())
    }

    pub fn transition_from_started_to_stopped(&mut self) -> Result<(), Error> {
        assert!(!self.is_dummy());
        assure!(self.lifecycle_state == HartLifecycleState::Started, Error::CannotStopNotStartedHart())?;
        self.lifecycle_state = HartLifecycleState::Stopped;
        Ok(())
    }

    pub fn transition_from_suspended_to_started(&mut self) -> Result<(), Error> {
        assert!(!self.is_dummy());
        assure!(self.lifecycle_state == HartLifecycleState::Suspended, Error::CannotStartNotSuspendedHart())?;
        self.lifecycle_state = HartLifecycleState::Started;
        Ok(())
    }

    pub fn transition_to_shutdown(&mut self) {
        assert!(!self.is_dummy());
        self.lifecycle_state = HartLifecycleState::Shutdown;
    }
}

impl ConfidentialHart {
    pub fn execute(&mut self, request: &InterHartRequest) {
        match request {
            InterHartRequest::SbiIpi(v) => v.execute_on_confidential_hart(self),
            InterHartRequest::SbiRemoteFenceI(v) => v.execute_on_confidential_hart(self),
            InterHartRequest::SbiRemoteSfenceVma(v) => v.execute_on_confidential_hart(self),
            InterHartRequest::SbiRemoteSfenceVmaAsid(v) => v.execute_on_confidential_hart(self),
            InterHartRequest::SbiRemoteHfenceGvmaVmid(v) => v.execute_on_confidential_hart(self),
            InterHartRequest::ShutdownRequest(_) => self.transition_to_shutdown(),
        }
    }
}
