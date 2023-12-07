// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::hart::HartState;

pub struct ConvertToConfidentialVm {
    hart_state: HartState,
}

impl ConvertToConfidentialVm {
    pub fn new(from_state: &HartState) -> Self {
        let hart_state = HartState::from_existing(0, from_state);
        Self { hart_state }
    }

    pub fn into(self) -> HartState {
        self.hart_state
    }
}
