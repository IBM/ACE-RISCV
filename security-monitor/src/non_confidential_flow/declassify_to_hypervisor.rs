// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::interrupts::{ExposeEnabledInterrupts, HandleInterrupt};
use crate::confidential_flow::handlers::mmio::{MmioLoadRequest, MmioStoreRequest};
use crate::confidential_flow::handlers::sbi::{SbiRequest, SbiResponse};

/// Declassifiers that expose part of the confidential VM's hart state to the hypervisor.
pub enum DeclassifyToHypervisor {
    SbiRequest(SbiRequest),
    SbiResponse(SbiResponse),
    Interrupt(HandleInterrupt),
    MmioLoadRequest(MmioLoadRequest),
    MmioStoreRequest(MmioStoreRequest),
    EnabledInterrupts(ExposeEnabledInterrupts),
}
