// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{
    ConfidentialHart, ConfidentialHartRemoteCommand, ConfidentialHartRemoteCommandExecutable, ControlDataStorage,
};

/// Handles a request from one confidential hart to execute IPI on other confidential harts.
#[derive(PartialEq, Debug, Clone)]
pub struct Ipi {
    hart_mask: usize,
    hart_mask_base: usize,
}

impl Ipi {
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
        let result = ControlDataStorage::try_confidential_vm_mut(confidential_flow.confidential_vm_id(), |mut confidential_vm| {
            confidential_flow.broadcast_remote_command(&mut confidential_vm, ConfidentialHartRemoteCommand::Ipi(self))
        })
        .map_or_else(|error| SbiResponse::error(error), |_| SbiResponse::success());
        confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(result))
    }
}

impl ConfidentialHartRemoteCommandExecutable for Ipi {
    fn execute_on_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        // IPI exposes itself as supervisor-level software interrupt.
        confidential_hart.csrs_mut().pending_irqs |= crate::core::architecture::riscv::specification::MIE_VSSIP_MASK;
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
