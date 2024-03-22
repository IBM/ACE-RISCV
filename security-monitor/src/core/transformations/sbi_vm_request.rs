// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GeneralPurposeRegister, HartArchitecturalState};
use crate::core::control_data::HardwareHart;
use crate::core::transformations::SbiRequest;

pub struct SbiVmRequest {
    sbi_request: SbiRequest,
}

impl SbiVmRequest {
    pub fn from_hardware_hart(hardware_hart: &HardwareHart) -> Self {
        Self {
            sbi_request: SbiRequest::new(
                hardware_hart.gprs().read(GeneralPurposeRegister::a7),
                hardware_hart.gprs().read(GeneralPurposeRegister::a6),
                hardware_hart.gprs().read(GeneralPurposeRegister::a0),
                hardware_hart.gprs().read(GeneralPurposeRegister::a1),
                hardware_hart.gprs().read(GeneralPurposeRegister::a2),
                hardware_hart.gprs().read(GeneralPurposeRegister::a3),
                hardware_hart.gprs().read(GeneralPurposeRegister::a4),
                hardware_hart.gprs().read(GeneralPurposeRegister::a5),
            ),
        }
    }

    pub fn sbi_request(&self) -> &SbiRequest {
        &self.sbi_request
    }
}
