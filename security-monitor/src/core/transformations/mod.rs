// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::interrupts::InterruptRequest;
use crate::confidential_flow::handlers::mmio::{
    MmioLoadPending, MmioLoadRequest, MmioLoadResult, MmioStorePending, MmioStoreRequest, MmioStoreResult,
};
use crate::confidential_flow::handlers::sbi::{SbiRequest, SbiResult};
use crate::confidential_flow::handlers::shared_page::SharePageRequest;
use crate::confidential_flow::handlers::shutdown::ShutdownRequest;
use crate::confidential_flow::handlers::smp::{
    SbiIpi, SbiRemoteFenceI, SbiRemoteHfenceGvmaVmid, SbiRemoteSfenceVma, SbiRemoteSfenceVmaAsid,
};
use crate::confidential_flow::handlers::virtual_instructions::VirtualInstructionResult;
use crate::non_confidential_flow::handlers::delegate_hypercall::SbiVmRequest;
use crate::non_confidential_flow::handlers::delegate_to_opensbi::OpensbiResult;

/// Transformation that modifies hypervisor state as a result of processing its own request
pub enum ExposeToHypervisor {
    SbiRequest(SbiRequest),
    SbiResult(SbiResult),
    SbiVmRequest(SbiVmRequest),
    OpensbiResult(OpensbiResult),
    Resume(),
}

/// Declassifiers that expose part of the confidential VM's hart state to the hypervisor.
pub enum DeclassifyToHypervisor {
    SbiRequest(SbiRequest),
    SbiResult(SbiResult),
    InterruptRequest(InterruptRequest),
    MmioLoadRequest(MmioLoadRequest),
    MmioStoreRequest(MmioStoreRequest),
}

pub enum ExposeToConfidentialVm {
    SbiResult(SbiResult),
    VirtualInstructionResult(VirtualInstructionResult),
    Nothing(),
}

/// Declassifiers that expose part of the hypervisor's state to a confidential VM's hart.
pub enum DeclassifyToConfidentialVm {
    SbiResult(SbiResult),
    MmioLoadResult(MmioLoadResult),
    MmioStoreResult(MmioStoreResult),
    Nothing(),
}

/// An intermediate confidential hart state that requested certain operation from the hypervisor and is waiting for the
/// response.
#[derive(PartialEq)]
pub enum PendingRequest {
    SharePage(SharePageRequest),
    MmioLoad(MmioLoadPending),
    MmioStore(MmioStorePending),
    SbiHsmHartStartPending(),
    SbiRequest(),
}

/// A request send from one confidential hart to another confidential hart belonging to the same confidential VM.
#[derive(Debug, PartialEq, Clone)]
pub enum InterHartRequest {
    SbiIpi(SbiIpi),
    SbiRemoteFenceI(SbiRemoteFenceI),
    SbiRemoteSfenceVma(SbiRemoteSfenceVma),
    SbiRemoteSfenceVmaAsid(SbiRemoteSfenceVmaAsid),
    SbiRemoteHfenceGvmaVmid(SbiRemoteHfenceGvmaVmid),
    ShutdownRequest(ShutdownRequest),
}

impl InterHartRequest {
    pub fn is_hart_selected(&self, hart_id: usize) -> bool {
        match self {
            Self::SbiIpi(v) => v.is_hart_selected(hart_id),
            Self::SbiRemoteFenceI(v) => v.is_hart_selected(hart_id),
            Self::SbiRemoteSfenceVma(v) => v.is_hart_selected(hart_id),
            Self::SbiRemoteSfenceVmaAsid(v) => v.is_hart_selected(hart_id),
            Self::SbiRemoteHfenceGvmaVmid(v) => v.is_hart_selected(hart_id),
            Self::ShutdownRequest(v) => v.initiating_confidential_hart_id() != hart_id,
        }
    }
}
