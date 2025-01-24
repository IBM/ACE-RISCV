// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::mmio::MmioAccessFault;
use crate::confidential_flow::handlers::sbi::{DelegateToConfidentialVm, SbiResponse};
use crate::confidential_flow::handlers::virtual_instructions::VirtualInstruction;

/// Transformation of the confidential hart state in a response to processing of a confidential hart call.
pub enum ApplyToConfidentialHart {
    MmioAccessFault(MmioAccessFault),
    SbiResponse(SbiResponse),
    VirtualInstruction(VirtualInstruction),
    DelegateToConfidentialVm(DelegateToConfidentialVm),
}
