// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::smp::SbiResult;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, ConfidentialVmId};
use crate::core::transformations::{ExposeToConfidentialVm, InterHartRequest};

#[derive(PartialEq, Debug, Clone)]
pub struct SbiIpi {
    hart_mask: usize,
    hart_mask_base: usize,
}

impl SbiIpi {
    pub fn new(hart_mask: usize, hart_mask_base: usize) -> Self {
        Self { hart_mask, hart_mask_base }
    }

    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let hart_mask = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        let hart_mask_base = confidential_hart.gprs().read(GeneralPurposeRegister::a1);
        Self { hart_mask, hart_mask_base }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        let transformation = confidential_flow
            .broadcast_inter_hart_request(InterHartRequest::SbiIpi(self))
            .and_then(|_| Ok(ExposeToConfidentialVm::SbiResult(SbiResult::success(0))))
            .unwrap_or_else(|error| error.into_confidential_transformation());
        confidential_flow.exit_to_confidential_hart(transformation)
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        // IPI exposes itself as supervisor-level software interrupt.
        confidential_hart.csrs_mut().vsip.enable_bit_on_saved_value(crate::core::architecture::MIE_VSSIP);
    }

    pub fn is_hart_selected(&self, hart_id: usize) -> bool {
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
