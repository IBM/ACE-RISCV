// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::HartArchitecturalState;

pub struct ConvertToConfidentialVm {
    hart_state: HartArchitecturalState,
}

impl ConvertToConfidentialVm {
    pub fn new(from_state: &HartArchitecturalState) -> Self {
        let hart_state = HartArchitecturalState::from_existing(0, from_state);
        Self { hart_state }
    }

    pub fn into(self) -> HartArchitecturalState {
        self.hart_state
    }
}
