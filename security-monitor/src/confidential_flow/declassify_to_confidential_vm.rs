// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::mmio::{MmioLoadResponse, MmioStoreResponse};
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::non_confidential_flow::handlers::cove_hypervisor_extension::RunConfidentialHart;

/// Declassifiers that expose part of the hypervisor's state to a confidential VM's hart.
pub enum DeclassifyToConfidentialVm {
    SbiResponse(SbiResponse),
    MmioLoadResponse(MmioLoadResponse),
    MmioStoreResponse(MmioStoreResponse),
    SetTimer(RunConfidentialHart),
}
