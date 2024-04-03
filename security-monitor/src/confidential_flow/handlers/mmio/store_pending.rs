// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

/// Information stored in the confidential hart that requested MMIO store and is waiting for the response.
pub struct MmioStorePending {
    instruction_length: usize,
}

impl MmioStorePending {
    pub fn new(instruction_length: usize) -> Self {
        Self { instruction_length }
    }

    pub fn instruction_length(&self) -> usize {
        self.instruction_length
    }
}
