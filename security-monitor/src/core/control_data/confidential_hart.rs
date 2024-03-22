// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GeneralPurposeRegister, HartArchitecturalState, HartLifecycleState, *};
use crate::core::control_data::ConfidentialVmId;
use crate::core::transformations::{ExposeToConfidentialVm, InterHartRequest, PendingRequest, SbiHsmHartStart, SbiHsmHartSuspend};
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
}

impl ConfidentialHart {
    /// Constructs a dummy hart. This dummy hart carries no confidential information. It is used to indicate that a real
    /// confidential hart has been assigned to a hardware hart for execution.
    pub fn dummy(id: usize) -> Self {
        // We set the lifecycle state of the dummy hart to `Started` because this state will be used as the state of the confidential hart
        // that has been assigned to physical hart. Specifically, after a confidential hart gets assigned to hardware hart, the confidential
        // VM will be left with a dummy hart. Any other code or request that will inspect the state of the (stolen) confidential hart, will
        // in reality look into the state of the dummy hart which will correctly say that the confidential hart is in the `Started` state.
        Self::new(HartArchitecturalState::empty(id), HartLifecycleState::Started)
    }

    /// Constructs a confidential hart with the state after a reset.
    pub fn from_vm_hart_reset(id: usize, non_confidential_hart_state: &HartArchitecturalState) -> Self {
        let mut confidential_hart_state = HartArchitecturalState::empty(id);
        confidential_hart_state.csrs.mstatus.save_value(non_confidential_hart_state.csrs.mstatus.read_value());
        // set timer counter to infinity
        confidential_hart_state.csrs.vstimecmp.save_value(usize::MAX - 1);
        // assume the same starting clock for all confidential harts within the same confidential VM
        confidential_hart_state.csrs.htimedelta.save_value(non_confidential_hart_state.csrs.htimedelta.read_value());
        confidential_hart_state.csrs.scounteren.save_value(non_confidential_hart_state.csrs.scounteren.read_value());
        Self::new(confidential_hart_state, HartLifecycleState::Stopped)
    }

    /// Constructs a confidential hart with the state of the non-confidential hart that made a call to promote the VM to confidential VM
    pub fn from_vm_hart(id: usize, non_confidential_hart_state: &HartArchitecturalState) -> Self {
        let hart_architectural_state = HartArchitecturalState::from_existing(id, &non_confidential_hart_state);
        let mut confidential_hart = Self::new(hart_architectural_state, HartLifecycleState::Started);
        confidential_hart.pending_request = Some(PendingRequest::SbiRequest());
        confidential_hart
    }

    /// Constructs a new confidential hart based on the given architectural state. It configures CSRs to a well-known initial state in which
    /// a confidential hart will execute securely.
    fn new(mut confidential_hart_state: HartArchitecturalState, lifecycle_state: HartLifecycleState) -> Self {
        confidential_hart_state.csrs.sstatus.save_value((1 << CSR_SSTATUS_SPIE) | (1 << CSR_SSTATUS_UXL) | (0b10 << CSR_SSTATUS_FS));
        confidential_hart_state.csrs.hstatus.save_value((1 << CSR_HSTATUS_VTW) | (1 << CSR_HSTATUS_SPVP) | (1 << CSR_HSTATUS_UXL));
        // Delegate VS-level interrupts directly to the confidential VM. All other interrupts will trap in the security monitor.
        confidential_hart_state.csrs.mideleg.save_value(MIE_VSSIP_MASK | MIE_VSTIP_MASK | MIE_VSEIP_MASK);
        confidential_hart_state.csrs.hideleg.save_value(confidential_hart_state.csrs.mideleg.read_value());
        // the `vsie` register reflects `hie`, so we set up `hie` allowing only VS-level interrupts
        confidential_hart_state.csrs.hie.save_value(confidential_hart_state.csrs.mideleg.read_value());
        // Allow only hypervisor's timer interrupts to preemt confidential VM's execution
        confidential_hart_state.csrs.mie.save_value(MIE_STIP_MASK);
        // Delegate exceptions that can be handled directly in the confidential VM
        confidential_hart_state.csrs.medeleg.save_value(
            (1 << CAUSE_MISALIGNED_FETCH)
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
                | (1 << CAUSE_STORE_PAGE_FAULT),
        );
        confidential_hart_state.csrs.hedeleg.save_value(confidential_hart_state.csrs.medeleg.read_value());
        // Setup the M-mode trap handler to the security monitor's entry point
        confidential_hart_state.csrs.mtvec.save_value(enter_from_confidential_hart_asm as usize);

        // TODO: clear CSRs that are not relevant for the confidential VM execution

        Self { confidential_vm_id: None, confidential_hart_state, lifecycle_state, pending_request: None }
    }

    pub fn set_confidential_vm_id(&mut self, confidential_vm_id: ConfidentialVmId) {
        self.confidential_vm_id = Some(confidential_vm_id);
    }

    pub fn confidential_vm_id(&self) -> Option<ConfidentialVmId> {
        self.confidential_vm_id
    }

    pub fn confidential_hart_id(&self) -> usize {
        self.confidential_hart_state.id
    }

    pub fn confidential_hart_state(&self) -> &HartArchitecturalState {
        &self.confidential_hart_state
    }

    pub fn confidential_hart_state_mut(&mut self) -> &mut HartArchitecturalState {
        &mut self.confidential_hart_state
    }

    pub fn take_request(&mut self) -> Option<PendingRequest> {
        self.pending_request.take()
    }

    pub fn is_dummy(&self) -> bool {
        self.confidential_vm_id.is_none()
    }

    /// Returns true if this confidential hart can be scheduled on the physical hart.
    pub fn is_executable(&self) -> bool {
        let hart_states_allowed_to_resume = [HartLifecycleState::Started, HartLifecycleState::StartPending, HartLifecycleState::Suspended];
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
    pub fn transition_from_stopped_to_start_pending(&mut self, request: SbiHsmHartStart) -> Result<(), Error> {
        assure_not!(self.is_dummy(), Error::HartAlreadyRunning())?;
        assure!(self.lifecycle_state == HartLifecycleState::Stopped, Error::CannotStartNotStoppedHart())?;

        // Let's set up the confidential hart initial state so that it can be run
        self.lifecycle_state = HartLifecycleState::StartPending;
        self.pending_request = Some(PendingRequest::SbiHsmHartStartPending());

        // Following the SBI documentation of the function `hart start` in the HSM extension, only vsatp, vsstatus.SIE,
        // a0, a1 have defined values, all other registers are in an undefined state. The hart will start
        // executing in the supervisor mode with disabled MMU (vsatp=0).
        self.confidential_hart_state.csrs.vsatp.save_value(0);
        // start the new confidential hart with interrupts disabled
        self.confidential_hart_state.csrs.mstatus.disable_bit_on_saved_value(CSR_MSTATUS_SPIE);
        self.confidential_hart_state.csrs.mstatus.disable_bit_on_saved_value(CSR_MSTATUS_MPIE);

        self.confidential_hart_state.csrs.vsstatus.disable_bit_on_saved_value(CSR_STATUS_SIE);
        self.confidential_hart_state.gprs.write(GeneralPurposeRegister::a0, self.confidential_hart_id());
        self.confidential_hart_state.gprs.write(GeneralPurposeRegister::a1, request.opaque());
        self.confidential_hart_state.csrs.mepc.save_value(request.start_address());

        Ok(())
    }

    /// Changes the lifecycle state of the confidential hart to the `Started` state.
    pub fn transition_from_start_pending_to_started(&mut self) {
        assert!(!self.is_dummy());
        if self.lifecycle_state == HartLifecycleState::StartPending {
            self.lifecycle_state = HartLifecycleState::Started;
        }
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
    pub fn apply(&mut self, transformation: ExposeToConfidentialVm) -> usize {
        match transformation {
            ExposeToConfidentialVm::SbiResult(v) => v.declassify_to_confidential_hart(self),
            ExposeToConfidentialVm::MmioLoadResult(v) => v.declassify_to_confidential_hart(self),
            ExposeToConfidentialVm::VirtualInstructionResult(v) => v.declassify_to_confidential_hart(self),
            ExposeToConfidentialVm::MmioStoreResult(v) => v.declassify_to_confidential_hart(self),
            ExposeToConfidentialVm::SbiHsmHartStartPending() => self.transition_from_start_pending_to_started(),
            ExposeToConfidentialVm::Resume() => {}
        }
        core::ptr::addr_of!(self.confidential_hart_state) as usize
    }

    pub fn execute(&mut self, request: &InterHartRequest) {
        match request {
            InterHartRequest::SbiIpi(v) => v.declassify_to_confidential_hart(self),
            InterHartRequest::SbiRemoteFenceI(v) => v.declassify_to_confidential_hart(self),
            InterHartRequest::SbiRemoteSfenceVma(v) => v.declassify_to_confidential_hart(self),
            InterHartRequest::SbiRemoteSfenceVmaAsid(v) => v.declassify_to_confidential_hart(self),
            InterHartRequest::SbiRemoteHfenceGvmaVmid(v) => v.declassify_to_confidential_hart(self),
            InterHartRequest::SbiSrstSystemReset(_) => self.transition_to_shutdown(),
        }
    }
}
