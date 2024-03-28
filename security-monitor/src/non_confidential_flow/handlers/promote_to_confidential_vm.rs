// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiRequest;
use crate::core::architecture::{GeneralPurposeRegister, HartArchitecturalState};
use crate::core::control_data::{
    ConfidentialHart, ConfidentialVm, ConfidentialVmId, ConfidentialVmMeasurement, ControlData, HypervisorHart,
};
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::core::memory_protector::ConfidentialVmMemoryProtector;
use crate::error::Error;
use crate::non_confidential_flow::{ApplyToHypervisor, NonConfidentialFlow};
use flattened_device_tree::FlattenedDeviceTree;

/// Our convention is to give the boot hart a fixed id.
const BOOT_HART_ID: usize = 0;

pub struct PromoteToConfidentialVm {
    hart_state: HartArchitecturalState,
}

impl PromoteToConfidentialVm {
    pub fn from_vm_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self { hart_state: HartArchitecturalState::from_existing(0, hypervisor_hart.hypervisor_hart_state()) }
    }

    /// Handles the `promote to confidential VM` call requested by the non-confidential VM via an environment call. The call traps in the
    /// security monitor as an `environment call from VS-mode` (see `mcause` register specification). In a response to this call, the
    /// security monitor creates a confidential VM and informs the hypervisor that the VM became a confidential VM. The hypervisor
    /// should then record this information and use dedicated entry point (`resume confidential hart` call) to execute particular
    /// confidential hart.
    ///
    /// # Security
    ///
    /// In case of a Linux kernel confidential VM, Linux kernel must make this call before 1) it uses parameters from the Linux command
    /// line, 2) before it changes the content of the VM's memory.
    ///
    /// # Safety
    ///
    /// The virtual machine must make this call on a boot hart before other harts come out of reset.
    pub fn handle(self, non_confidential_flow: NonConfidentialFlow) -> ! {
        debug!("Promoting a VM into a confidential VM");
        let transformation = match self.create_confidential_vm() {
            Ok(id) => ApplyToHypervisor::SbiRequest(SbiRequest::kvm_ace_register(id, BOOT_HART_ID)),
            Err(error) => {
                debug!("Promotion to confidential VM failed: {:?}", error);
                error.into_non_confidential_transformation()
            }
        };
        non_confidential_flow.apply_and_exit_to_hypervisor(transformation)
    }

    fn create_confidential_vm(&self) -> Result<ConfidentialVmId, Error> {
        // The pointer to the flattened device tree (FDT) as well as the entire FDT must be treated as an untrusted input, which measurement
        // is reflected during attestation. Only after moving VM's data (and the FDT) to the confidential memory, we can check if
        // the pointer is valid, i.e., it points to a valid address in the confidential VM's address space.

        // Copy the entire VM's state to the confidential memory, recreating the MMU configuration.
        let memory_protector = ConfidentialVmMemoryProtector::from_vm_state(&self.hart_state)?;

        // Below use of unsafe is ok because (1) the security monitor owns the memory region containing the data of the not-yet-created
        // confidential VM's and (2) there is only one physical hart executing this code.
        let fdt_address_in_confidential_memory = unsafe { memory_protector.translate_address(&self.fdt_address())?.to_ptr() };
        // We parse untrusted FDT using an external library. A vulnerability in this library might blow up the security!
        // Below unsafe is ok because it is the start of the entire page which is at least 4KiB in size (see safety requirements of
        // `FlattenedDeviceTree::from_raw_pointer`).
        let device_tree = unsafe { FlattenedDeviceTree::from_raw_pointer(fdt_address_in_confidential_memory)? };

        // We create a fixed number of harts (all but the boot hart are in the reset state) according to the FDT configuration. An
        // alternative approach (to discuss) is to create just a boot hart and then allow creation of more harts when getting a call
        // from the confidential VM to start a hart.
        let number_of_confidential_harts = device_tree.harts().count();
        assure!(number_of_confidential_harts < ConfidentialVm::MAX_NUMBER_OF_HARTS_PER_VM, Error::ReachedMaxNumberOfHartsPerVm())?;
        let confidential_harts = (0..number_of_confidential_harts)
            .map(|confidential_hart_id| match confidential_hart_id {
                0 => ConfidentialHart::from_vm_hart(confidential_hart_id, &self.hart_state),
                _ => ConfidentialHart::from_vm_hart_reset(confidential_hart_id, &self.hart_state),
            })
            .collect();

        // TODO: measure the confidential VM
        let measurements = [ConfidentialVmMeasurement::empty(); 4];

        // TODO: perform local attestation (optional) if there is a `confidential VM's blob`

        let confidential_vm_id = ControlData::try_write(|control_data| {
            // We have a write lock on the entire control data! Spend as little time here as possible because we are
            // blocking all other harts from accessing the control data. This influences all confidential VMs in the system!
            let id = control_data.unique_id()?;
            let confidential_vm = ConfidentialVm::new(id, confidential_harts, measurements, memory_protector);
            control_data.insert_confidential_vm(confidential_vm)
        })?;

        debug!("Created new confidential VM[id={:?}]", confidential_vm_id);

        Ok(confidential_vm_id)
    }

    /// Returns the address of the device tree provided as the first argument of the call.
    fn fdt_address(&self) -> ConfidentialVmPhysicalAddress {
        ConfidentialVmPhysicalAddress::new(self.hart_state.gprs.read(GeneralPurposeRegister::a0))
    }
}
