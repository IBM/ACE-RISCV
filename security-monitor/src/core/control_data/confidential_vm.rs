// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::HartLifecycleState;
use crate::core::control_data::{
    ConfidentialHart, ConfidentialHartRemoteCommand, ConfidentialVmId, ConfidentialVmMmioRegion, HardwareHart, StaticMeasurements,
};
use crate::core::memory_protector::ConfidentialVmMemoryProtector;
use crate::error::Error;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use riscv_cove_tap::Secret;
use spin::{Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard};

pub struct ConfidentialVm {
    id: ConfidentialVmId,
    confidential_harts: Vec<RwLock<ConfidentialHart>>,
    _measurements: StaticMeasurements,
    secrets: Vec<Secret>,
    remote_commands: BTreeMap<usize, Mutex<Vec<ConfidentialHartRemoteCommand>>>,
    memory_protector: RwLock<ConfidentialVmMemoryProtector>,
    allowed_external_interrupts: usize,
    mmio_regions: Vec<ConfidentialVmMmioRegion>,
}

impl ConfidentialVm {
    pub const MAX_NUMBER_OF_HARTS_PER_VM: usize = 1024;
    /// An average number of inter hart requests that can be buffered before being processed.
    const AVG_NUMBER_OF_COMMANDS: usize = 3;
    /// A maximum number of inter hart requests that can be buffered.
    const MAX_NUMBER_OF_COMMANDS: usize = 64;
    /// A maximum number of MMIO regions that a confidential VM can register
    const MAX_NUMBER_OF_MMIO_REGIONS: usize = 1024;

    /// Constructs a new confidential VM.
    ///
    /// # Safety
    ///
    /// The id of the confidential VM must be unique.
    pub fn new(
        id: ConfidentialVmId, mut confidential_harts: Vec<ConfidentialHart>, _measurements: StaticMeasurements, secrets: Vec<Secret>,
        mut memory_protector: ConfidentialVmMemoryProtector,
    ) -> Self {
        memory_protector.set_confidential_vm_id(id);
        let remote_commands = confidential_harts
            .iter_mut()
            .map(|confidential_hart| {
                confidential_hart.set_confidential_vm_id(id);
                (confidential_hart.confidential_hart_id(), Mutex::new(Vec::with_capacity(Self::AVG_NUMBER_OF_COMMANDS)))
            })
            .collect();
        Self {
            id,
            confidential_harts: confidential_harts.into_iter().map(|h| RwLock::new(h)).collect(),
            _measurements,
            secrets,
            remote_commands,
            memory_protector: RwLock::new(memory_protector),
            allowed_external_interrupts: 0,
            mmio_regions: Vec::with_capacity(8),
        }
    }

    pub fn confidential_vm_id(&self) -> ConfidentialVmId {
        self.id
    }

    pub fn memory_protector(&self) -> RwLockReadGuard<'_, ConfidentialVmMemoryProtector> {
        self.memory_protector.read()
    }

    pub fn memory_protector_mut(&self) -> RwLockWriteGuard<'_, ConfidentialVmMemoryProtector> {
        self.memory_protector.write()
    }

    pub fn secret(&self, secret_id: usize) -> Result<Vec<u8>, Error> {
        self.secrets
            .iter()
            .find(|ref s| s.name == secret_id as u64)
            .and_then(|s| Some(s.value.to_vec()))
            .ok_or_else(|| Error::InvalidParameter())
    }

    pub(super) fn deallocate(self) {
        self.memory_protector.into_inner().into_root_page_table().deallocate();
    }
}

/* Heavy context switches */
impl ConfidentialVm {
    /// Assigns a confidential hart of the confidential VM to the hardware hart. The hardware memory isolation mechanism
    /// is reconfigured to enforce memory access control for the confidential VM. Returns error if the confidential VM's
    /// virtual hart has been already stolen or is in the `Stopped` state.
    pub fn steal_confidential_hart(&self, confidential_hart_id: usize, hardware_hart: &mut HardwareHart) -> Result<(), Error> {
        ensure!(confidential_hart_id < self.confidential_harts.len(), Error::InvalidHartId())?;
        let mut confidential_hart = self.confidential_harts[confidential_hart_id].write();
        // The hypervisor might try to schedule the same confidential hart on different physical harts. We detect it
        // because after a confidential_hart is scheduled for the first time, its token is stolen and the
        // ConfidentialVM is left with a dummy confidential_hart. A dummy confidential hart is a hart not associated
        // with any confidential vm.
        ensure_not!(confidential_hart.is_dummy(), Error::HartAlreadyRunning())?;
        // The hypervisor might try to schedule a confidential hart that has never been started. This is forbidden.
        ensure!(confidential_hart.is_executable(), Error::HartNotExecutable())?;
        // Assign the confidential hart to the hardware hart. The code below this line must not throw an error!
        core::mem::swap(hardware_hart.confidential_hart_mut(), &mut confidential_hart);
        // Reconfigure the hardware memory isolation mechanism to enforce that the confidential virtual machine has access only to the
        // memory regions it owns. Below invocation is safe because we are now in the confidential flow part of the finite state
        // machine and the virtual hart is assigned to the hardware hart.
        unsafe { self.memory_protector().enable() };
        Ok(())
    }

    /// Unassigns a confidential hart from the hardware hart. The confidential hart is stored back in the confidential VM. The dummy hart
    /// that was stored as a placeholder in the confidential VM is given back to the hardware hart.
    pub fn return_confidential_hart(&self, hardware_hart: &mut HardwareHart) {
        assert!(!hardware_hart.confidential_hart().is_dummy());
        assert!(Some(self.id) == hardware_hart.confidential_hart().confidential_vm_id());
        let confidential_hart_id = hardware_hart.confidential_hart().confidential_hart_id();
        assert!(self.confidential_harts.len() > confidential_hart_id);
        // Return the confidential hart to the confidential machine.
        core::mem::swap(hardware_hart.confidential_hart_mut(), &mut self.confidential_harts[confidential_hart_id].write());
    }
}

/* Interrupt related */
impl ConfidentialVm {
    pub fn allowed_external_interrupts(&self) -> usize {
        self.allowed_external_interrupts
    }

    pub fn allow_external_interrupt(&mut self, external_interrupt: usize) {
        self.allowed_external_interrupts |= external_interrupt;
    }
}

/* Management of MMIO regions */
impl ConfidentialVm {
    pub fn add_mmio_region(&mut self, region: ConfidentialVmMmioRegion) -> Result<(), Error> {
        ensure!(self.mmio_regions.len() < Self::MAX_NUMBER_OF_MMIO_REGIONS, Error::ReachedMaxNumberOfMmioRegions())?;
        ensure!(!self.mmio_regions.iter().any(|x| x.overlaps(&region)), Error::OverlappingMmioRegion())?;
        Ok(self.mmio_regions.push(region))
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
    pub fn is_vm_executing(&self) -> bool {
        self.confidential_harts.iter().filter(|hart| hart.read().is_dummy()).count() == 0
    }

    /// Returns the lifecycle state of the confidential hart
    pub fn confidential_hart_lifecycle_state(&self, confidential_hart_id: usize) -> Result<HartLifecycleState, Error> {
        Ok(self.confidential_harts.get(confidential_hart_id).ok_or(Error::InvalidHartId())?.read().lifecycle_state().clone())
    }

    /// Transits the confidential hart's lifecycle state to `StartPending`. Returns error if the confidential hart is
    /// not in the `Stopped` state or a confidential hart with the requested id does not exist.
    pub fn start_confidential_hart(&self, confidential_hart_id: usize, start_address: usize, opaque: usize) -> Result<(), Error> {
        self.confidential_harts
            .get(confidential_hart_id)
            .ok_or(Error::InvalidHartId())?
            .write()
            .transition_from_stopped_to_started(start_address, opaque)
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
    pub fn broadcast_remote_command(
        &self, sender_confidential_hart_id: usize, remote_command: ConfidentialHartRemoteCommand,
    ) -> Result<usize, Error> {
        (0..self.confidential_harts.len())
            .filter(|confidential_hart_id| remote_command.is_hart_selected(*confidential_hart_id))
            .filter(|confidential_hart_id| *confidential_hart_id != sender_confidential_hart_id)
            .map(|confidential_hart_id| {
                let (is_executable, mask) = {
                    let confidential_hart = self.confidential_harts[confidential_hart_id].read();
                    (confidential_hart.is_executable(), confidential_hart.hardware_hart_id().and_then(|id| Some(1 << id)).unwrap_or(0))
                };
                if is_executable {
                    self.try_confidential_hart_remote_commands(confidential_hart_id, |ref mut remote_commands| {
                        ensure!(remote_commands.len() < Self::MAX_NUMBER_OF_COMMANDS, Error::ReachedMaxNumberOfRemoteCommands())?;
                        if remote_commands.iter().find(|c| **c == remote_command).is_none() {
                            remote_commands.push(remote_command.clone());
                        }
                        Ok(())
                    })?;
                }
                Ok(mask)
            })
            .try_fold(0, |acc, x: Result<usize, Error>| Ok(acc | x?))
    }

    pub fn try_confidential_hart_remote_commands<F, O>(&self, confidential_hart_id: usize, op: O) -> Result<F, Error>
    where O: FnOnce(MutexGuard<'_, Vec<ConfidentialHartRemoteCommand>>) -> Result<F, Error> {
        op(self.remote_commands.get(&confidential_hart_id).ok_or(Error::InvalidHartId())?.lock())
    }
}
