// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::{is_bit_enabled, GeneralPurposeRegister};
use crate::core::transformations::{
    ExposeToConfidentialVm, ExposeToHypervisor, MmioLoadPending, MmioLoadRequest, MmioLoadResult, MmioStorePending, MmioStoreRequest,
    MmioStoreResult, PendingRequest,
};
use crate::error::Error;

pub fn request_mmio_load(confidential_flow: ConfidentialFlow) -> ! {
    match MmioLoadRequest::from_confidential_hart(confidential_flow.confidential_hart()) {
        Ok(mmio_request) => confidential_flow
            .set_pending_request(PendingRequest::MmioLoad(MmioLoadPending::new(mmio_request.instruction_length(), mmio_request.gpr())))
            .into_non_confidential_flow()
            .exit_to_hypervisor(ExposeToHypervisor::MmioLoadRequest(mmio_request)),
        Err(error) => confidential_flow.into_non_confidential_flow().exit_to_hypervisor(error.into_non_confidential_transformation()),
    }
}

pub fn request_mmio_store(confidential_flow: ConfidentialFlow) -> ! {
    match MmioStoreRequest::from_confidential_hart(confidential_flow.confidential_hart()) {
        Ok(mmio_request) => confidential_flow
            .set_pending_request(PendingRequest::MmioStore(MmioStorePending::new(mmio_request.instruction_length())))
            .into_non_confidential_flow()
            .exit_to_hypervisor(ExposeToHypervisor::MmioStoreRequest(mmio_request)),
        Err(error) => confidential_flow.into_non_confidential_flow().exit_to_hypervisor(error.into_non_confidential_transformation()),
    }
}

pub fn handle_mmio_load_response(confidential_flow: ConfidentialFlow, result: MmioLoadPending) -> ! {
    let result = MmioLoadResult::from_hardware_hart(confidential_flow.hardware_hart(), result);
    confidential_flow.exit_to_confidential_hart(ExposeToConfidentialVm::MmioLoadResult(result))
}

pub fn handle_mmio_store_response(confidential_flow: ConfidentialFlow, result: MmioStorePending) -> ! {
    let transformation = ExposeToConfidentialVm::MmioStoreResult(MmioStoreResult::new(result));
    confidential_flow.exit_to_confidential_hart(transformation)
}
