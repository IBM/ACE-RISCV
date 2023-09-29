// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::transformations::GuestStorePageFaultRequest;

#[derive(PartialEq)]
pub struct GuestStorePageFaultResult {
    instruction_length: usize,
}

impl GuestStorePageFaultResult {
    pub fn new(request: GuestStorePageFaultRequest) -> Self {
        Self {
            instruction_length: request.instruction_length(),
        }
    }

    pub fn instruction_length(&self) -> usize {
        self.instruction_length
    }
}
