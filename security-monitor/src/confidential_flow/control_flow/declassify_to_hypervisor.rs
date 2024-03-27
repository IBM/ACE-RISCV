// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::interrupts::InterruptRequest;
use crate::confidential_flow::handlers::mmio::{MmioLoadRequest, MmioStoreRequest};
use crate::confidential_flow::handlers::sbi::{SbiRequest, SbiResult};

/// Declassifiers that expose part of the confidential VM's hart state to the hypervisor.
pub enum DeclassifyToHypervisor {
    SbiRequest(SbiRequest),
    SbiResult(SbiResult),
    InterruptRequest(InterruptRequest),
    MmioLoadRequest(MmioLoadRequest),
    MmioStoreRequest(MmioStoreRequest),
}
