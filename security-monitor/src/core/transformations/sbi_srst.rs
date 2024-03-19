// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(PartialEq, Debug, Clone)]
pub struct SbiSrstSystemReset {
    initiating_confidential_hart_id: usize,
}

impl SbiSrstSystemReset {
    pub fn new(initiating_confidential_hart_id: usize) -> Self {
        Self { initiating_confidential_hart_id }
    }

    pub fn initiating_confidential_hart_id(&self) -> usize {
        self.initiating_confidential_hart_id
    }
}
