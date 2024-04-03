// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::handlers::virtual_instructions::VirtualInstruction;

/// Transformation of the confidential hart state created as a result of processing a confidential hart call.
pub enum ApplyToConfidentialHart {
    SbiResponse(SbiResponse),
    VirtualInstruction(VirtualInstruction),
}
