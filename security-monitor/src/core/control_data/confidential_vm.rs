// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ConfidentialHart, HardwareHart};
use crate::core::interrupt_controller::InterruptController;
use crate::core::memory_protector::ConfidentialVmMemoryProtector;
use crate::core::transformations::InterHartRequest;
use crate::error::Error;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use spin::{Mutex, MutexGuard};

const MAX_HASH_SIZE: usize = 512; // 512b for SHA-512

pub struct ConfidentialVm {
    id: ConfidentialVmId,
    _measurements: [Measurement; 4],
    confidential_harts: Vec<ConfidentialHart>,
    memory_protector: ConfidentialVmMemoryProtector,
    inter_hart_requests: BTreeMap<usize, Mutex<Vec<InterHartRequest>>>,
}

impl ConfidentialVm {
    const AVG_NUMBER_OF_REMOTE_HART_REQUESTS: usize = 3;
    const MAX_NUMBER_OF_REMOTE_HART_REQUESTS: usize = 256;

    pub fn new(
        id: ConfidentialVmId, mut confidential_harts: Vec<ConfidentialHart>,
        mut memory_protector: ConfidentialVmMemoryProtector,
    ) -> Self {
        memory_protector.set_confidential_vm_id(id);
        let mut inter_hart_requests = BTreeMap::new();
        confidential_harts.iter_mut().for_each(|confidential_hart| {
            confidential_hart.set_confidential_vm_id(id);
            let inter_hart_requests_buffer = Mutex::new(Vec::with_capacity(Self::AVG_NUMBER_OF_REMOTE_HART_REQUESTS));
            inter_hart_requests.insert(confidential_hart.confidential_hart_id(), inter_hart_requests_buffer);
        });
        Self { id, _measurements: [Measurement::empty(); 4], confidential_harts, memory_protector, inter_hart_requests }
    }

    pub fn memory_protector_mut(&mut self) -> &mut ConfidentialVmMemoryProtector {
        &mut self.memory_protector
    }

    /// Steals a confidential hart from the confidential VM and assigns it to the hardware hart. The hardware memory
    /// isolation mechanism is reconfigured to enforce memory access control for the confidential VM. Returns error if
    /// the confidential VM's virtual hart has been already stolen.
    ///
    /// Guarantees:
    /// * If confidential hart is assigned to the hardware hart, then the hardware hart is configured to enforce memory
    ///   access control of the confidential VM.
    pub fn steal_confidential_hart(
        &mut self, confidential_hart_id: usize, hardware_hart: &mut HardwareHart,
    ) -> Result<(), Error> {
        let confidential_hart = self.confidential_harts.get(confidential_hart_id).ok_or(Error::InvalidHartId())?;
        // The hypervisor might try to schedule the same confidential hart on different physical harts. We detect it
        // because after a confidential_hart is scheduled for the first time, its token is stolen and the
        // ConfidentialVM is left with a dummy confidential_hart. A dummy confidential hart is a hart not associated
        // with any confidential vm.
        assure_not!(confidential_hart.is_dummy(), Error::RunningVHart())?;
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

    pub fn is_running(&self) -> bool {
        self.confidential_harts.iter().filter(|confidential_hart| confidential_hart.is_dummy()).count() > 0
    }

    /// Queues a request to other confidential hart and emits a hardware interrupt to the physical hart that executes
    /// that confidential hart. If the confidential hart is not executing, then no hardware interrupt is emmited.
    /// Returns error when 1) a queue that stores the confidential hart's InterHartRequests is full, 2) when sending an IPI failed.
    pub fn add_inter_hart_request(&self, inter_hart_request: InterHartRequest) -> Result<(), Error> {
        (0..self.confidential_harts.len())
            .filter(|confidential_hart_id| inter_hart_request.is_hart_selected(*confidential_hart_id))
            .try_for_each(|confidential_hart_id| {
                self.try_inter_hart_requests(confidential_hart_id, |ref mut inter_hart_requests| {
                    assure!(
                        inter_hart_requests.len() < Self::MAX_NUMBER_OF_REMOTE_HART_REQUESTS,
                        Error::ReachedMaxNumberOfRemoteHartRequests()
                    )?;
                    inter_hart_requests.push(inter_hart_request.clone());
                    // TODO: should we also inject IPI so that the interrupted confidential hart is aware of the inter
                    // hart request?
                    Ok(())
                })?;

                let hart = &self.confidential_harts[confidential_hart_id];
                if hart.is_dummy() {
                    // The confidential hart that should receive an InterHartRequest is currently running on a hardware
                    // hart. We interrupt that hardware hart with IPI. Consequently, that hardware
                    // hart will trap into the security monitor that will execute InterHartRequests
                    // on the targetted confidential hart.
                    let id_of_hardware_hart_running_confidential_hart = hart.confidential_hart_id();
                    InterruptController::try_read(|interrupt_controller| {
                        interrupt_controller.send_ipi(id_of_hardware_hart_running_confidential_hart)
                    })?;
                }
                Ok(())
            })
    }

    pub fn try_inter_hart_requests<F, O>(&self, confidential_hart_id: usize, op: O) -> Result<F, Error>
    where O: FnOnce(MutexGuard<'_, Vec<InterHartRequest>>) -> Result<F, Error> {
        op(self.inter_hart_requests.get(&confidential_hart_id).ok_or(Error::InvalidHartId())?.lock())
    }
}

#[derive(PartialEq, Eq, Hash, Debug, PartialOrd, Ord, Copy, Clone)]
pub struct ConfidentialVmId(usize);

impl ConfidentialVmId {
    pub fn new(value: usize) -> Self {
        Self(value)
    }

    pub fn usize(&self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy)]
pub struct Measurement {
    pub value: [u8; MAX_HASH_SIZE / 8],
}

impl Measurement {
    pub const fn empty() -> Measurement {
        Self { value: [0u8; MAX_HASH_SIZE / 8] }
    }
}
