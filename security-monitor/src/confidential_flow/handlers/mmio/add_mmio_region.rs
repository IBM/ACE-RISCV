// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::ConfidentialHart;

pub struct AddMmioRegion {
    region_start_address: usize,
    region_length: usize,
}

impl AddMmioRegion {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self {
            region_start_address: confidential_hart.gprs().read(GeneralPurposeRegister::a0),
            region_length: confidential_hart.gprs().read(GeneralPurposeRegister::a1),
        }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        // TODO: make sure region_start_address is aligned to 4KiB
        // TODO: make sure the region_start_address is a valid guest address
        // TODO: make sure this region does not overlap with any other previously defined region
        let transformation = ApplyToConfidentialHart::SbiResponse(SbiResponse::success(0));
        confidential_flow.apply_and_exit_to_confidential_hart(transformation)
    }
}
