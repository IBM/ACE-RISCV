// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::HartLifecycleState;
use crate::core::control_data::{ConfidentialHart, ConfidentialVmId, ConfidentialVmMeasurement, HardwareHart};
use crate::core::interrupt_controller::InterruptController;
use crate::core::memory_protector::ConfidentialVmMemoryProtector;
use crate::core::transformations::{InterHartRequest, SbiHsmHartStart};
use crate::error::Error;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use spin::{Mutex, MutexGuard};

pub struct ConfidentialVm {
    id: ConfidentialVmId,
    measurements: [ConfidentialVmMeasurement; 4],
    confidential_harts: Vec<ConfidentialHart>,
    memory_protector: ConfidentialVmMemoryProtector,
    inter_hart_requests: BTreeMap<usize, Mutex<Vec<InterHartRequest>>>,
}

impl ConfidentialVm {
    /// An average number of inter hart requests that are buffered before being processed.
    const AVG_NUMBER_OF_REMOTE_HART_REQUESTS: usize = 3;
    /// A maximum number of inter hart requests that can be buffered.
    const MAX_NUMBER_OF_REMOTE_HART_REQUESTS: usize = 64;

    /// Constructs a new confidential VM.
    ///
    /// Safety:
    /// * The id of the confidential VM must be unique.
    pub fn new(
        id: ConfidentialVmId, mut confidential_harts: Vec<ConfidentialHart>, measurements: [ConfidentialVmMeasurement; 4],
        mut memory_protector: ConfidentialVmMemoryProtector,
    ) -> Self {
        memory_protector.set_confidential_vm_id(id);
        let mut inter_hart_requests = BTreeMap::new();
        confidential_harts.iter_mut().for_each(|confidential_hart| {
            confidential_hart.set_confidential_vm_id(id);
            let inter_hart_requests_buffer = Mutex::new(Vec::with_capacity(Self::AVG_NUMBER_OF_REMOTE_HART_REQUESTS));
            inter_hart_requests.insert(confidential_hart.confidential_hart_id(), inter_hart_requests_buffer);
        });
        Self { id, measurements, confidential_harts, memory_protector, inter_hart_requests }
    }

    pub fn confidential_vm_id(&self) -> ConfidentialVmId {
        self.id
    }

    pub fn memory_protector_mut(&mut self) -> &mut ConfidentialVmMemoryProtector {
        &mut self.memory_protector
    }

    /// Assigns a confidential hart of the confidential VM to the hardware hart. The hardware memory isolation mechanism
    /// is reconfigured to enforce memory access control for the confidential VM. Returns error if the confidential VM's
    /// virtual hart has been already stolen or is in the `Stopped` state.
    ///
    /// Guarantees:
    /// * If confidential hart is assigned to the hardware hart, then the hardware hart is configured to enforce memory access control of
    ///   the confidential VM.
    pub fn steal_confidential_hart(&mut self, confidential_hart_id: usize, hardware_hart: &mut HardwareHart) -> Result<(), Error> {
        let confidential_hart = self.confidential_harts.get(confidential_hart_id).ok_or(Error::InvalidHartId())?;
        // The hypervisor might try to schedule the same confidential hart on different physical harts. We detect it
        // because after a confidential_hart is scheduled for the first time, its token is stolen and the
        // ConfidentialVM is left with a dummy confidential_hart. A dummy confidential hart is a hart not associated
        // with any confidential vm.
        assure_not!(confidential_hart.is_dummy(), Error::HartAlreadyRunning())?;
        // The hypervisor might try to schedule a confidential hart that has never been started. This is forbidden.
        assure!(confidential_hart.is_executable(), Error::HartNotExecutable())?;
        // We can now assign the confidential hart to the hardware hart. The code below this line must not throw an
        // error.
        core::mem::swap(&mut hardware_hart.confidential_hart, &mut self.confidential_harts[confidential_hart_id]);
        // It is safe to invoke below unsafe code because at this point we are in the confidential flow part of the
        // finite state machine and the virtual hart is assigned to the hardware hart. We must reconfigure the hardware
        // memory isolation mechanism to enforce that the confidential virtual machine has access only to the memory
        // regions it owns.
        unsafe { self.memory_protector.enable() };
        Ok(())
    }

    /// Unassigns a confidential hart from the hardware hart.
    ///
    /// Safety:
    /// * A confidential hart belonging to this confidential VM is assigned to the hardware hart.
    pub fn return_confidential_hart(&mut self, hardware_hart: &mut HardwareHart) {
        assert!(!hardware_hart.confidential_hart.is_dummy());
        assert!(Some(self.id) == hardware_hart.confidential_hart().confidential_vm_id());
        let confidential_hart_id = hardware_hart.confidential_hart.confidential_hart_id();
        assert!(self.confidential_harts.len() > confidential_hart_id);
        core::mem::swap(&mut hardware_hart.confidential_hart, &mut self.confidential_harts[confidential_hart_id]);
        // It is safe to reconfigure the memory access control configuration to enable access to memory regions owned
        // by the hypervisor because we are now transitioning into the non-confidential flow part of the finite state
        // machine where the hardware hart is associated with a dummy virtual hart.
        unsafe { hardware_hart.enable_hypervisor_memory_protector() };
    }

    pub fn are_all_harts_shutdown(&self) -> bool {
        self.confidential_harts.iter().filter(|confidential_hart| !confidential_hart.is_shutdown()).count() == 0
    }

    /// Transits the confidential hart's lifecycle state to `StartPending`. Returns error if the confidential hart is
    /// not in the `Stopped` state or a confidential hart with the requested id does not exist.
    pub fn transit_confidential_hart_to_start_pending(&mut self, request: SbiHsmHartStart) -> Result<(), Error> {
        let hart = self.confidential_harts.get_mut(request.confidential_hart_id).ok_or(Error::InvalidHartId())?;
        hart.transition_from_stopped_to_start_pending(request)?;
        Ok(())
    }

    /// Queues a request from one confidential hart to another and emits a hardware interrupt to the physical hart that
    /// executes that confidential hart. If the confidential hart is not executing, then no hardware interrupt is
    /// emmited.
    ///
    /// Returns error when 1) a queue that stores the confidential hart's InterHartRequests is full, 2) when sending an
    /// IPI failed.
    pub fn broadcast_inter_hart_request(&mut self, inter_hart_request: InterHartRequest) -> Result<(), Error> {
        (0..self.confidential_harts.len())
            .filter(|confidential_hart_id| inter_hart_request.is_hart_selected(*confidential_hart_id))
            .try_for_each(|confidential_hart_id| {
                let is_assigned_to_hardware_hart = { self.confidential_harts[confidential_hart_id].is_dummy() };
                if !is_assigned_to_hardware_hart {
                    // The confidential hart that should receive an InterHartRequest is not running on any hardware
                    // hart. Thus, we can apply the InterHartRequest directly.
                    let transition = inter_hart_request.clone().into_expose_to_confidential_vm();
                    self.confidential_harts[confidential_hart_id].apply(transition);
                } else {
                    // The confidential hart that should receive an InterHartRequest is currently running on a hardware
                    // hart. We add the InterHartRequest to a per confidential hart queue and then interrupt that
                    // hardware hart with IPI. Consequently, the hardware hart running the target confidential hart will
                    // trap into the security monitor, which will execute InterHartRequests on the targetted
                    // confidential hart.
                    self.try_inter_hart_requests(confidential_hart_id, |ref mut inter_hart_requests| {
                        assure!(
                            inter_hart_requests.len() < Self::MAX_NUMBER_OF_REMOTE_HART_REQUESTS,
                            Error::ReachedMaxNumberOfRemoteHartRequests()
                        )?;
                        inter_hart_requests.push(inter_hart_request.clone());
                        // TODO: should we also inject IPI so that the interrupted confidential hart is aware of the
                        // inter hart request?
                        Ok(())
                    })?;
                    let confidential_hart = &self.confidential_harts[confidential_hart_id];
                    let id_of_hardware_hart_running_confidential_hart = confidential_hart.confidential_hart_id();
                    InterruptController::try_read(|interrupt_controller| {
                        interrupt_controller.send_ipi(id_of_hardware_hart_running_confidential_hart)
                    })?;
                }
                Ok(())
            })
    }

    /// Returns the lifecycle state of the confidential hart
    pub fn confidential_hart_lifecycle_state(&self, confidential_hart_id: usize) -> Result<HartLifecycleState, Error> {
        assure!(confidential_hart_id < self.confidential_harts.len(), Error::InvalidHartId())?;
        Ok(self.confidential_harts[confidential_hart_id].lifecycle_state().clone())
    }

    pub fn try_inter_hart_requests<F, O>(&mut self, confidential_hart_id: usize, op: O) -> Result<F, Error>
    where O: FnOnce(MutexGuard<'_, Vec<InterHartRequest>>) -> Result<F, Error> {
        op(self.inter_hart_requests.get(&confidential_hart_id).ok_or(Error::InvalidHartId())?.lock())
    }
}
