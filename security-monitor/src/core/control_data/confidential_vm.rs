// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::HartLifecycleState;
use crate::core::control_data::{
    ConfidentialHart, ConfidentialHartRemoteCommand, ConfidentialVmId, ConfidentialVmMmioRegion, HardwareHart, StaticMeasurements,
};
use crate::core::interrupt_controller::InterruptController;
use crate::core::memory_protector::ConfidentialVmMemoryProtector;
use crate::error::Error;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use spin::{Mutex, MutexGuard};

pub struct ConfidentialVm {
    id: ConfidentialVmId,
    measurements: StaticMeasurements,
    confidential_harts: Vec<ConfidentialHart>,
    confidential_hart_remote_commands: BTreeMap<usize, Mutex<Vec<ConfidentialHartRemoteCommand>>>,
    memory_protector: ConfidentialVmMemoryProtector,
    allowed_external_interrupts: usize,
    mmio_regions: Vec<ConfidentialVmMmioRegion>,
}

impl ConfidentialVm {
    pub const MAX_NUMBER_OF_HARTS_PER_VM: usize = 1024;
    /// An average number of inter hart requests that can be buffered before being processed.
    const AVG_NUMBER_OF_REMOTE_HART_REQUESTS: usize = 3;
    /// A maximum number of inter hart requests that can be buffered.
    const MAX_NUMBER_OF_REMOTE_HART_REQUESTS: usize = 64;
    /// A maximum number of MMIO regions that a confidential VM can register
    const MAX_NUMBER_OF_MMIO_REGIONS: usize = 1024;

    /// Constructs a new confidential VM.
    ///
    /// # Safety
    ///
    /// The id of the confidential VM must be unique.
    pub fn new(
        id: ConfidentialVmId, mut confidential_harts: Vec<ConfidentialHart>, measurements: StaticMeasurements,
        mut memory_protector: ConfidentialVmMemoryProtector,
    ) -> Self {
        memory_protector.set_confidential_vm_id(id);
        let confidential_hart_remote_commands = confidential_harts
            .iter_mut()
            .map(|confidential_hart| {
                confidential_hart.set_confidential_vm_id(id);
                (confidential_hart.confidential_hart_id(), Mutex::new(Vec::with_capacity(Self::AVG_NUMBER_OF_REMOTE_HART_REQUESTS)))
            })
            .collect();
        let mmio_regions = Vec::with_capacity(8);
        Self {
            id,
            measurements,
            confidential_harts,
            memory_protector,
            confidential_hart_remote_commands,
            allowed_external_interrupts: 0,
            mmio_regions,
        }
    }

    pub fn confidential_vm_id(&self) -> ConfidentialVmId {
        self.id
    }

    pub fn memory_protector_mut(&mut self) -> &mut ConfidentialVmMemoryProtector {
        &mut self.memory_protector
    }

    pub(super) fn deallocate(self) {
        self.memory_protector.into_root_page_table().deallocate();
    }
}

/* Heavy context switches */
impl ConfidentialVm {
    /// Assigns a confidential hart of the confidential VM to the hardware hart. The hardware memory isolation mechanism
    /// is reconfigured to enforce memory access control for the confidential VM. Returns error if the confidential VM's
    /// virtual hart has been already stolen or is in the `Stopped` state.
    ///
    /// # Guarantees
    ///
    /// The physical hart is configured to enforce memory access control so that the confidential VM has access only to its own memory.
    pub fn steal_confidential_hart(&mut self, confidential_hart_id: usize, hardware_hart: &mut HardwareHart) -> Result<(), Error> {
        let confidential_hart = self.confidential_harts.get(confidential_hart_id).ok_or(Error::InvalidHartId())?;
        // The hypervisor might try to schedule the same confidential hart on different physical harts. We detect it
        // because after a confidential_hart is scheduled for the first time, its token is stolen and the
        // ConfidentialVM is left with a dummy confidential_hart. A dummy confidential hart is a hart not associated
        // with any confidential vm.
        ensure_not!(confidential_hart.is_dummy(), Error::HartAlreadyRunning())?;
        // The hypervisor might try to schedule a confidential hart that has never been started. This is forbidden.
        ensure!(confidential_hart.is_executable(), Error::HartNotExecutable())?;

        // Heavy context switch:
        // 1) Dump control and status registers (CSRs) of the hypervisor hart to the main memory.
        hardware_hart.hypervisor_hart_mut().save_in_main_memory();

        // 2) Load control and status registers (CSRs) of confidential hart from the physical hart executing this code.
        self.confidential_harts[confidential_hart_id].restore_from_main_memory();

        // Assign the confidential hart to the hardware hart. The code below this line must not throw an error!
        core::mem::swap(hardware_hart.confidential_hart_mut(), &mut self.confidential_harts[confidential_hart_id]);

        // Reconfigure the hardware memory isolation mechanism to enforce that the confidential virtual machine has access only to the
        // memory regions it owns. Below invocation is safe because we are now in the confidential flow part of the finite state
        // machine and the virtual hart is assigned to the hardware hart.
        unsafe { self.memory_protector.enable() };

        Ok(())
    }

    /// Unassigns a confidential hart from the hardware hart. The confidential hart is stored back in the confidential VM. The dummy hart
    /// that was stored as a placeholder in the confidential VM is given back to the hardware hart.
    ///
    /// # Safety
    ///
    /// A confidential hart belongs to this confidential VM and is currently assigned to the hardware hart.
    pub fn return_confidential_hart(&mut self, hardware_hart: &mut HardwareHart) {
        assert!(!hardware_hart.confidential_hart().is_dummy());
        assert!(Some(self.id) == hardware_hart.confidential_hart().confidential_vm_id());
        let confidential_hart_id = hardware_hart.confidential_hart().confidential_hart_id();
        assert!(self.confidential_harts.len() > confidential_hart_id);

        // Return the confidential hart to the confidential machine.
        core::mem::swap(hardware_hart.confidential_hart_mut(), &mut self.confidential_harts[confidential_hart_id]);

        // Heavy context switch:
        // 1) Dump control and status registers (CSRs) of the confidential hart to the main memory.
        self.confidential_harts[confidential_hart_id].save_in_main_memory();

        // 2) Load control and status registers (CSRs) of the hypervisor hart into the physical hart executing this code.
        hardware_hart.hypervisor_hart_mut().restore_from_main_memory();

        // Reconfigure the memory access control configuration to enable access to memory regions owned by the hypervisor because we
        // are now transitioning into the non-confidential flow part of the finite state machine where the hardware hart is
        // associated with a dummy virtual hart.
        // It is safe to invoke below unsafe code because at this point we are transitioning from the confidential flow part of the
        // finite state machine to the non-confidential part and the virtual hart is still assigned to the hardware hart.
        unsafe { hardware_hart.hypervisor_hart().enable_hypervisor_memory_protector() };
    }
}

/* Interrupt related */
impl ConfidentialVm {
    pub fn allowed_external_interrupts(&self) -> usize {
        self.allowed_external_interrupts
    }

    pub fn set_allowed_external_interrupts(&mut self, allowed_external_interrupts: usize) {
        self.allowed_external_interrupts |= allowed_external_interrupts;
    }
}

/* Management of untrusted MMIO regions */
impl ConfidentialVm {
    pub fn add_mmio_region(&mut self, region: ConfidentialVmMmioRegion) -> Result<(), Error> {
        ensure!(self.mmio_regions.len() < Self::MAX_NUMBER_OF_MMIO_REGIONS, Error::ReachedMaxNumberOfMmioRegions())?;
        ensure!(!self.mmio_regions.iter().any(|x| x.overlaps(&region)), Error::OverlappingMmioRegion())?;
        self.mmio_regions.push(region);
        Ok(())
    }

    pub fn remove_mmio_region(&mut self, region: &ConfidentialVmMmioRegion) {
        self.mmio_regions.retain(|x| !x.overlaps(region));
    }

    pub fn is_mmio_region_defined(&self, region: &ConfidentialVmMmioRegion) -> bool {
        self.mmio_regions.iter().any(|x| x.contains(region))
    }
}

/* Lifecycle related */
impl ConfidentialVm {
    pub fn are_all_harts_shutdown(&self) -> bool {
        self.confidential_harts.iter().filter(|hart| hart.lifecycle_state() != &HartLifecycleState::PoweredOff).count() == 0
    }

    /// Returns the lifecycle state of the confidential hart
    pub fn confidential_hart_lifecycle_state(&self, confidential_hart_id: usize) -> Result<HartLifecycleState, Error> {
        ensure!(confidential_hart_id < self.confidential_harts.len(), Error::InvalidHartId())?;
        Ok(self.confidential_harts[confidential_hart_id].lifecycle_state().clone())
    }

    /// Transits the confidential hart's lifecycle state to `StartPending`. Returns error if the confidential hart is
    /// not in the `Stopped` state or a confidential hart with the requested id does not exist.
    pub fn start_confidential_hart(&mut self, confidential_hart_id: usize, start_address: usize, opaque: usize) -> Result<(), Error> {
        let hart = self.confidential_harts.get_mut(confidential_hart_id).ok_or(Error::InvalidHartId())?;
        hart.transition_from_stopped_to_started(start_address, opaque)
    }
}

/* Remote commands */
impl ConfidentialVm {
    /// Queues a request from one confidential hart to another and emits a hardware interrupt to the physical hart that
    /// executes that confidential hart. If the confidential hart is not executing, then no hardware interrupt is
    /// emmited.
    ///
    /// Returns error when 1) a queue that stores the confidential hart's ConfidentialHartRemoteCommands is full, 2) when sending an
    /// IPI failed.
    pub fn broadcast_remote_command(&mut self, confidential_hart_remote_command: ConfidentialHartRemoteCommand) -> Result<(), Error> {
        (0..self.confidential_harts.len())
            .filter(|confidential_hart_id| confidential_hart_remote_command.is_hart_selected(*confidential_hart_id))
            .try_for_each(|confidential_hart_id| {
                let is_assigned_to_hardware_hart = self.confidential_harts[confidential_hart_id].is_dummy();
                if !is_assigned_to_hardware_hart {
                    // The confidential hart that should receive the ConfidentialHartRemoteCommand is not running on any hardware
                    // hart. Thus, we can excute the ConfidentialHartRemoteCommand directly.
                    self.confidential_harts[confidential_hart_id].execute(&confidential_hart_remote_command);
                } else {
                    // The confidential hart that should receive an ConfidentialHartRemoteCommand is currently running on a hardware
                    // hart. We add the ConfidentialHartRemoteCommand to a per confidential hart queue and then interrupt that
                    // hardware hart with IPI. Consequently, the hardware hart running the target confidential hart will
                    // trap into the security monitor, which will execute ConfidentialHartRemoteCommands on the targetted
                    // confidential hart.
                    self.try_confidential_hart_remote_commands(confidential_hart_id, |ref mut confidential_hart_remote_commands| {
                        ensure!(
                            confidential_hart_remote_commands.len() < Self::MAX_NUMBER_OF_REMOTE_HART_REQUESTS,
                            Error::ReachedMaxNumberOfRemoteHartRequests()
                        )?;
                        confidential_hart_remote_commands.push(confidential_hart_remote_command.clone());
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

    pub fn try_confidential_hart_remote_commands<F, O>(&mut self, confidential_hart_id: usize, op: O) -> Result<F, Error>
    where O: FnOnce(MutexGuard<'_, Vec<ConfidentialHartRemoteCommand>>) -> Result<F, Error> {
        op(self.confidential_hart_remote_commands.get(&confidential_hart_id).ok_or(Error::InvalidHartId())?.lock())
    }
}
