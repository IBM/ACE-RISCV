// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::hart::HartState;
use riscv::register::hgatp::Hgatp;

pub struct EsmRequest {
    hgatp: Hgatp,
    hart_state: HartState,
}

impl EsmRequest {
    pub fn new(from_state: &HartState) -> Self {
        let hart_state = HartState::from_existing(0, from_state);
        let hgatp = Hgatp::from(from_state.hgatp);
        Self { hgatp, hart_state }
    }

    pub fn into(self) -> (Hgatp, HartState) {
        (self.hgatp, self.hart_state)
    }
}
