// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, InterHartRequest, InterHartRequestExecutable};

/// Handles a request from one confidential hart to execute IPI on other confidential harts.
#[derive(PartialEq, Debug, Clone)]
pub struct SbiIpi {
    hart_mask: usize,
    hart_mask_base: usize,
}

impl SbiIpi {
    pub fn new(hart_mask: usize, hart_mask_base: usize) -> Self {
        Self { hart_mask, hart_mask_base }
    }

    pub fn all_harts() -> Self {
        Self::new(usize::MAX, usize::MAX)
    }

    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let hart_mask = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        let hart_mask_base = confidential_hart.gprs().read(GeneralPurposeRegister::a1);
        Self { hart_mask, hart_mask_base }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        let transformation = confidential_flow
            .broadcast_inter_hart_request(InterHartRequest::SbiIpi(self))
            .and_then(|_| Ok(SbiResponse::success(0)))
            .unwrap_or_else(|error| SbiResponse::failure(error.code()));
        confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(transformation))
    }
}

impl InterHartRequestExecutable for SbiIpi {
    fn execute_on_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        // IPI exposes itself as supervisor-level software interrupt.
        confidential_hart.csrs_mut().vsip.enable_bit_on_saved_value(crate::core::architecture::MIE_VSSIP);
    }

    fn is_hart_selected(&self, hart_id: usize) -> bool {
        // according to SBI documentation all harts are selected when the mask_base is of its maximum value
        match self.hart_mask_base == usize::MAX {
            true => true,
            false => hart_id
                .checked_sub(self.hart_mask_base)
                .filter(|id| *id < usize::BITS as usize)
                .is_some_and(|id| self.hart_mask & (1 << id) != 0),
        }
    }
}
