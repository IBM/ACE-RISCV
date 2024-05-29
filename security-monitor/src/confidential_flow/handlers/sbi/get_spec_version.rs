// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::control_data::ConfidentialHart;

pub struct SbiGetSpecVersion {}

impl SbiGetSpecVersion {
    const SBI_ECALL_VERSION_MAJOR: usize = 2;
    const SBI_ECALL_VERSION_MINOR: usize = 0;
    const SBI_SPEC_VERSION_MAJOR_OFFSET: usize = 24;
    const SBI_SPEC_VERSION_MAJOR_MASK: usize = 0x7f;

    pub fn from_confidential_hart(_: &ConfidentialHart) -> Self {
        Self {}
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let transformation = ApplyToConfidentialHart::SbiResponse(SbiResponse::success_with_code(Self::version()));
        confidential_flow.apply_and_exit_to_confidential_hart(transformation)
    }

    fn version() -> usize {
        ((Self::SBI_ECALL_VERSION_MAJOR << Self::SBI_SPEC_VERSION_MAJOR_OFFSET)
            & (Self::SBI_SPEC_VERSION_MAJOR_MASK << Self::SBI_SPEC_VERSION_MAJOR_OFFSET))
            | Self::SBI_ECALL_VERSION_MINOR
    }
}
