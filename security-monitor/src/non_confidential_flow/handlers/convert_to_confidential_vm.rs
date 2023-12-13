// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ConfidentialHart, ConfidentialVmId, ControlData};
use crate::core::memory_protector::ConfidentialVmMemoryProtector;
use crate::core::transformations::{ConvertToConfidentialVm, ExposeToHypervisor, SbiRequest};
use crate::error::Error;
use crate::non_confidential_flow::NonConfidentialFlow;

const BOOT_HART_ID: usize = 0;

pub fn handle(
    convert_to_confidential_vm_request: ConvertToConfidentialVm, non_confidential_flow: NonConfidentialFlow,
) -> ! {
    debug!("Converting a virtual machine into a confidential virtual machine");
    let transformation = match create_confidential_vm(convert_to_confidential_vm_request) {
        Ok(id) => ExposeToHypervisor::SbiRequest(SbiRequest::kvm_ace_register(id, BOOT_HART_ID)),
        Err(error) => error.into_non_confidential_transformation(),
    };
    non_confidential_flow.exit_to_hypervisor(transformation)
}

fn create_confidential_vm(
    convert_to_confidential_vm_request: ConvertToConfidentialVm,
) -> Result<ConfidentialVmId, Error> {
    let hart_state = convert_to_confidential_vm_request.into();
    let memory_protector = ConfidentialVmMemoryProtector::from_vm_state(&hart_state)?;
    // TODO: read number of harts from fdt
    let confidential_harts_count = 1;

    let confidential_harts = (0..confidential_harts_count)
        .map(|confidential_hart_id| match confidential_hart_id {
            0 => ConfidentialHart::from_vm_hart(confidential_hart_id, &hart_state),
            _ => ConfidentialHart::from_vm_hart_reset(confidential_hart_id, &hart_state),
        })
        .collect();

    // TODO: measure the confidential VM

    // TODO: perform local attestation (optional)

    let confidential_vm_id = ControlData::store_confidential_vm(confidential_harts, memory_protector)?;

    debug!("Created new confidential VM[id={:?}]", confidential_vm_id);

    Ok(confidential_vm_id)
}
