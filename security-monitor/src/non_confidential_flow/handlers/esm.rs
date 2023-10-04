// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ConfidentialHart, ConfidentialVmId, ControlData};
use crate::core::memory_tracker::NonConfidentialMemoryAddress;
use crate::core::mmu::{PagingSystem, RootPageTable};
use crate::core::transformations::{EsmRequest, ExposeToHypervisor, SbiRequest};
use crate::error::Error;
use crate::non_confidential_flow::NonConfidentialFlow;

const BOOT_HART_ID: usize = 0;

pub fn handle(esm_request: EsmRequest, non_confidential_flow: NonConfidentialFlow) -> ! {
    debug!("Handling enter secure mode (ESM) SM-call");
    let transformation = match create_confidential_vm(esm_request) {
        Ok(id) => ExposeToHypervisor::SbiRequest(SbiRequest::kvm_ace_register(id, BOOT_HART_ID)),
        Err(error) => error.into_non_confidential_transformation(),
    };
    non_confidential_flow.exit_to_hypervisor(transformation)
}

fn create_confidential_vm(esm_request: EsmRequest) -> Result<ConfidentialVmId, Error> {
    let (hgatp, hart_state) = esm_request.into();
    let paging_mode = hgatp.mode().ok_or_else(|| Error::UnsupportedPagingMode())?;
    let paging_system = PagingSystem::from(&paging_mode).ok_or_else(|| Error::UnsupportedPagingMode())?;
    let root_page_address = NonConfidentialMemoryAddress::new(hgatp.address())?;
    // TODO: read number of harts from fdt
    let confidential_harts_count = 1;

    let root_page_table = RootPageTable::copy_from_non_confidential_memory(root_page_address, paging_system)?;

    // create virtual processor for this confidential VM
    let confidential_harts = (0..confidential_harts_count)
        .map(|confidential_hart_id| match confidential_hart_id {
            0 => ConfidentialHart::from_vm_hart(confidential_hart_id, &hart_state),
            _ => ConfidentialHart::from_vm_hart_reset(confidential_hart_id, &hart_state),
        })
        .collect();

    // TODO: measure the confidential VM

    // TODO: perform local attestation (optional)

    let confidential_vm_id = ControlData::store_confidential_vm(confidential_harts, root_page_table)?;

    debug!("Created new confidential VM[id={:?}]", confidential_vm_id);

    Ok(confidential_vm_id)
}
