// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::control_data::ConfidentialHart;

pub struct RemoveMmioRegion {}

impl RemoveMmioRegion {
    pub fn from_confidential_hart(_confidential_hart: &ConfidentialHart) -> Self {
        Self {}
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let transformation = ApplyToConfidentialHart::SbiResponse(SbiResponse::success(0));
        confidential_flow.apply_and_exit_to_confidential_hart(transformation)
    }
}
