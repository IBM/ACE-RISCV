// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::sbi::NaclSharedMemory;
use crate::core::architecture::{GeneralPurposeRegister, Hgatp, PageSize};
use crate::core::control_data::{
    ConfidentialHart, ConfidentialVm, ConfidentialVmId, ControlDataStorage, HypervisorHart, StaticMeasurements,
};
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::core::memory_protector::ConfidentialVmMemoryProtector;
use crate::core::page_allocator::{Allocated, Page, PageAllocator};
use crate::error::Error;
use crate::non_confidential_flow::handlers::supervisor_binary_interface::SbiResponse;
use crate::non_confidential_flow::{ApplyToHypervisorHart, NonConfidentialFlow};
use alloc::vec::Vec;
use flattened_device_tree::FlattenedDeviceTree;
use tap::{TapSecret, TeeAttestationPayload, TeeAttestationPayloadParser};

/// Creates a confidential VM in a single-step. This handler implements the Promote to TVM call defined by the COVH ABI in the CoVE
/// specification. With this call, the hypervisor presents a state of a virtual machine, requesting the security monitor to promote it to a
/// confidential VM. The security monitor copies the VM state (data, page tables, boot hart state) into the confidential memory and measures
/// it.
///
/// # Safety
///
/// * The virtual machine initial state must consist of only one hart (boot hart) running. All other hart must be still in reset state.
/// * The address of the flattened device tree must be aligned to 8 bytes.
/// * The address of the authentication blob must be either `0` or aligned to 8 bytes.
pub struct PromoteToConfidentialVm {
    fdt_address: ConfidentialVmPhysicalAddress,
    tee_attestation_payload_address: Option<ConfidentialVmPhysicalAddress>,
    program_counter: usize,
    hgatp: Hgatp,
}

impl PromoteToConfidentialVm {
    const FDT_ALIGNMENT_IN_BYTES: usize = 8;
    const TAP_ALIGNMENT_IN_BYTES: usize = 4;
    const BOOT_HART_ID: usize = 0;

    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        let fdt_address = ConfidentialVmPhysicalAddress::new(hypervisor_hart.gprs().read(GeneralPurposeRegister::a0));
        let tee_attestation_payload_address = match hypervisor_hart.gprs().read(GeneralPurposeRegister::a1) {
            0 => None,
            address => Some(ConfidentialVmPhysicalAddress::new(address)),
        };
        let program_counter = hypervisor_hart.gprs().read(GeneralPurposeRegister::a2);
        let hgatp = Hgatp::from(hypervisor_hart.csrs().hgatp.read());
        Self { fdt_address, tee_attestation_payload_address, program_counter, hgatp }
    }

    pub fn handle(self, non_confidential_flow: NonConfidentialFlow) -> ! {
        let transformation = match self.create_confidential_vm(non_confidential_flow.shared_memory()) {
            Ok(confidential_vm_id) => {
                debug!("Created new confidential VM[id={:?}]", confidential_vm_id);
                SbiResponse::success_with_code(confidential_vm_id.usize())
            }
            Err(error) => {
                debug!("Promotion to confidential VM failed: {:?}", error);
                SbiResponse::error(error)
            }
        };
        non_confidential_flow.apply_and_exit_to_hypervisor(ApplyToHypervisorHart::SbiResponse(transformation))
    }

    fn create_confidential_vm(&self, shared_memory: &NaclSharedMemory) -> Result<ConfidentialVmId, Error> {
        debug!("Promoting a VM to a confidential VM");
        debug!("Copying the entire VM's state to the confidential memory, recreating the MMU configuration");
        let memory_protector = ConfidentialVmMemoryProtector::from_vm_state(&self.hgatp)?;

        // The pointer to the flattened device tree (FDT) as well as the entire FDT must be treated as an untrusted input, which measurement
        // is reflected during attestation. We can parse FDT only after moving VM's data (and the FDT) to the confidential memory.
        let number_of_confidential_harts = self.process_device_tree(&memory_protector)?;

        // TODO: generate htimedelta
        let htimedelta = 0;

        // We create a fixed number of harts (all but the boot hart are in the reset state).
        debug!("Copying boot hart's state");
        let confidential_harts: Vec<_> = (0..number_of_confidential_harts)
            .map(|confidential_hart_id| match confidential_hart_id {
                Self::BOOT_HART_ID => ConfidentialHart::from_vm_hart(confidential_hart_id, self.program_counter, htimedelta, shared_memory),
                _ => ConfidentialHart::from_vm_hart_reset(confidential_hart_id, htimedelta, shared_memory),
            })
            .collect();

        let tee_attestation_payload = self.read_tee_attestation_payload(&memory_protector)?;

        let measured_pages_digest = memory_protector.measure()?;
        let confidential_hart_digest = confidential_harts[Self::BOOT_HART_ID].measure();
        let measurements = StaticMeasurements::new(measured_pages_digest, confidential_hart_digest);
        debug!("VM measurements: {:?}", measurements);

        let secrets = self.authenticate_and_authorize_vm(tee_attestation_payload, &measurements)?;

        ControlDataStorage::try_write(|control_data| {
            // We have a write lock on the entire control data! Spend here as little time as possible because we are
            // blocking all other harts from accessing the control data. This influences all confidential VMs in the system!
            let id = control_data.unique_id()?;
            control_data.insert_confidential_vm(ConfidentialVm::new(id, confidential_harts, measurements, secrets, memory_protector))
        })
    }

    fn process_device_tree(&self, memory_protector: &ConfidentialVmMemoryProtector) -> Result<usize, Error> {
        debug!("Reading flatten device tree (FDT) at memory address 0x{:?}", self.fdt_address);
        let address_in_confidential_memory = memory_protector.translate_address(&self.fdt_address)?;
        // Make sure that the address is 8-bytes aligned. Once we ensure this, we can safely read 8 bytes because they must be within
        // the page boundary. These 8 bytes should contain the `magic` (first 4 bytes) and `size` (next 4 bytes).
        ensure!(address_in_confidential_memory.is_aligned_to(Self::FDT_ALIGNMENT_IN_BYTES), Error::FdtNotAlignedTo64Bits())?;
        // Below use of unsafe is ok because (1) the security monitor owns the memory region containing the data of the not-yet-created
        // confidential VM's and (2) there is only one physical hart executing this code.
        let fdt_total_size = unsafe { FlattenedDeviceTree::total_size(address_in_confidential_memory.to_ptr())? };
        ensure!(fdt_total_size >= FlattenedDeviceTree::FDT_HEADER_SIZE, Error::FdtInvalidSize())?;

        // To work with FDT, we must have it as a continous chunk of memory. We accept only FDTs that fit within 2MiB
        ensure!(fdt_total_size.div_ceil(PageSize::Size2MiB.in_bytes()) == 1, Error::FdtInvalidSize())?;
        let large_page = Self::relocate(memory_protector, &self.fdt_address, fdt_total_size, false)?;

        // Security note: We parse untrusted FDT using an external library. A vulnerability in this library might blow up our security
        // guarantees! Below unsafe is ok because FDT address is at least size of the FDT header and all FDT is in a continuous chunk of
        // memory. See the safety requirements of `FlattenedDeviceTree::from_raw_pointer`.
        let number_of_confidential_harts = match unsafe { FlattenedDeviceTree::from_raw_pointer(large_page.address().to_ptr()) } {
            Ok(device_tree) => device_tree.harts().count(),
            Err(_) => 0,
        };

        // Clean up, deallocate pages
        PageAllocator::release_pages(alloc::vec![large_page.deallocate()]);

        ensure!(number_of_confidential_harts > 0, Error::InvalidNumberOfHartsInFdt())?;
        ensure!(number_of_confidential_harts < ConfidentialVm::MAX_NUMBER_OF_HARTS_PER_VM, Error::InvalidNumberOfHartsInFdt())?;
        Ok(number_of_confidential_harts)
    }

    fn read_tee_attestation_payload(
        &self, memory_protector: &ConfidentialVmMemoryProtector,
    ) -> Result<Option<TeeAttestationPayload>, Error> {
        match self.tee_attestation_payload_address {
            Some(tee_attestation_payload_address) => {
                debug!("Reading TEE attestation payload (TAP) at memory address {:?}", tee_attestation_payload_address);
                let address_in_confidential_memory = memory_protector.translate_address(&tee_attestation_payload_address)?;
                // Make sure that the address is 8-bytes aligned. Once we ensure this, we can safely read 8 bytes because they must be
                // within the page boundary. These 8 bytes should contain the `magic` (first 4 bytes) and `size` (next 4
                // bytes).
                ensure!(address_in_confidential_memory.is_aligned_to(Self::TAP_ALIGNMENT_IN_BYTES), Error::AuthBlobNotAlignedTo32Bits())?;
                // Below use of unsafe is ok because (1) the security monitor owns the memory region containing the data of the
                // not-yet-created confidential VM's and (2) there is only one physical hart executing this code.
                let header: u64 =
                    unsafe { address_in_confidential_memory.read_volatile().try_into().map_err(|_| Error::AuthBlobNotAlignedTo32Bits())? };
                let total_size = ((header >> 16) & 0xFFFF) as usize + tap::ACE_HEADER_SIZE;
                // To work with the authentication blob, we must have it as a continous chunk of memory. We accept only authentication blobs
                // that fit within 2MiB
                ensure!(total_size.div_ceil(PageSize::Size2MiB.in_bytes()) == 1, Error::AuthBlobInvalidSize())?;
                let large_page = Self::relocate(memory_protector, &tee_attestation_payload_address, total_size, true)?;

                // TODO: we should parse to the blob key that will allow to unlock the lockbox.
                let mut parser = unsafe { TeeAttestationPayloadParser::from_raw_pointer(large_page.address().to_ptr(), total_size)? };
                let tee_attestation_payload = parser.parse_and_verify()?;

                // Clean up, deallocate pages
                PageAllocator::release_pages(alloc::vec![large_page.deallocate()]);

                Ok(Some(tee_attestation_payload))
            }
            None => Ok(None),
        }
    }

    /// Performs local attestation. It decides if the VM can be promote into a confidential VM and decrypts the attestation secret intended
    /// for this confidential VM.
    fn authenticate_and_authorize_vm(
        &self, tee_attestation_payload: Option<TeeAttestationPayload>, measurements: &StaticMeasurements,
    ) -> Result<Vec<TapSecret>, Error> {
        match tee_attestation_payload {
            Some(tee_attestation_payload) => {
                debug!("Authenticating and authorizing the confidential VM using read TAP");
                debug!("TAP contains {} lockboxes", tee_attestation_payload.lockboxes.len());
                debug!("TAP contains {} secrets", tee_attestation_payload.secrets.len());
                for digest in tee_attestation_payload.digests.iter() {
                    debug!("TAP digest: {:?} {:?} {}", digest.entry_type, digest.algorithm, digest.value_in_hex());
                    // TODO: make sure we compare digests of the same algorithm...
                    use crate::core::control_data::MeasurementDigest;
                    let pcr_value = MeasurementDigest::clone_from_slice(&digest.value);
                    ensure!(measurements.compare(digest.entry_type.to_u16() as usize, pcr_value)?, Error::LocalAttestationFailed())?;
                }
                debug!("Attestation successful");
                Ok(tee_attestation_payload.secrets)
            }
            None => Ok(alloc::vec![]),
        }
    }

    /// Copies a buffer into a single large page. The input buffer is continuous across guest physical pages with G-stage address
    /// translation enabled but might not be continuous across the real physical pages. The output buffer is continous accross real
    /// physical pages. Returns error if (1) the buffer to copy is larger than 2 MiB page, or (2) the base address is not aligned to
    /// 8-bytes. The caller is responsible for deallocating the page.
    fn relocate(
        memory_protector: &ConfidentialVmMemoryProtector, base_address: &ConfidentialVmPhysicalAddress, number_of_bytes_to_copy: usize,
        clear: bool,
    ) -> Result<Page<Allocated>, Error> {
        ensure!((base_address.usize() as *const u8).is_aligned_to(core::mem::size_of::<usize>()), Error::AddressNotAligned())?;
        let mut large_page = PageAllocator::acquire_page(PageSize::Size2MiB)?.zeroize();
        // Let's copy a blob from confidential VM's pages into the newly allocated huge page. We will copy in chunks of 8-bytes (usize).
        let mut copied_bytes = 0;
        while copied_bytes < number_of_bytes_to_copy {
            let confidential_vm_physical_address = base_address.add(copied_bytes);
            let confidential_memory_address = memory_protector.translate_address(&confidential_vm_physical_address)?;
            let value: usize = unsafe { confidential_memory_address.read_volatile() };
            if clear {
                unsafe { confidential_memory_address.write_volatile(0) };
            }
            large_page.write(copied_bytes, value)?;
            copied_bytes += core::mem::size_of::<usize>();
        }
        Ok(large_page)
    }
}
