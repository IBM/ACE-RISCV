// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::*;
use crate::core::control_data::ConfidentialHart;

pub struct SbiGetMimpid {}

impl SbiGetMimpid {
    pub fn from_confidential_hart(_: &ConfidentialHart) -> Self {
        Self {}
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let mimpid = CSR.mimpid.read();
        let transformation = ApplyToConfidentialHart::SbiResponse(SbiResponse::success(mimpid));
        confidential_flow.apply_and_exit_to_confidential_hart(transformation)
    }
}
