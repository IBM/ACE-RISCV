// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use interrupt::{EnabledInterrupts, InjectedInterrupts, InterruptRequest};
pub use mmio_pending::{MmioLoadPending, MmioStorePending};
pub use mmio_requests::{MmioLoadRequest, MmioStoreRequest};
pub use mmio_responses::{MmioLoadResult, MmioStoreResult};
pub use opensbi::{OpensbiRequest, OpensbiResult};
pub use promote_to_confidential_vm_request::PromoteToConfidentialVm;
pub use resume_request::ResumeRequest;
pub use sbi_call::{SbiRequest, SbiResult};
pub use sbi_vm_request::SbiVmRequest;
pub use shared_page::{SharePageRequest, SharePageResult, UnsharePageRequest};
pub use shutdown::{SbiSrstSystemReset, TerminateRequest};
pub use smp::{
    SbiHsmHartStart, SbiHsmHartStatus, SbiHsmHartSuspend, SbiIpi, SbiRemoteFenceI, SbiRemoteHfenceGvmaVmid, SbiRemoteSfenceVma,
    SbiRemoteSfenceVmaAsid,
};
pub use virtual_instruction::{VirtualInstructionRequest, VirtualInstructionResult};

mod interrupt;
mod mmio_pending;
mod mmio_requests;
mod mmio_responses;
mod opensbi;
mod promote_to_confidential_vm_request;
mod resume_request;
mod sbi_call;
mod sbi_vm_request;
mod shared_page;
mod shutdown;
mod smp;
mod virtual_instruction;

/// Declassifiers that expose part of the confidential VM's hart state to the hypervisor.
pub enum ExposeToHypervisor {
    SbiRequest(SbiRequest),
    SbiResult(SbiResult),
    OpensbiResult(OpensbiResult),
    SbiVmRequest(SbiVmRequest),
    MmioLoadRequest(MmioLoadRequest),
    MmioStoreRequest(MmioStoreRequest),
    InterruptRequest(InterruptRequest),
    EnabledInterrupts(EnabledInterrupts),
}

/// Declassifiers that expose part of the hypervisor's state to a confidential VM's hart.
pub enum ExposeToConfidentialVm {
    SbiResult(SbiResult),
    MmioLoadResult(MmioLoadResult),
    VirtualInstructionResult(VirtualInstructionResult),
    MmioStoreResult(MmioStoreResult),
    Resume(),
    SbiIpi(),
    SbiRemoteFenceI(SbiRemoteFenceI),
    SbiRemoteSfenceVma(SbiRemoteSfenceVma),
    SbiRemoteSfenceVmaAsid(SbiRemoteSfenceVmaAsid),
    SbiRemoteHfenceGvmaVmid(SbiRemoteHfenceGvmaVmid),
    SbiHsmHartStart(),
    SbiHsmHartStartPending(),
    SbiSrstSystemReset(),
}

/// An intermediate confidential hart state that requested certain operation from the hypervisor and is waiting for the
/// response.
#[derive(PartialEq)]
pub enum PendingRequest {
    SharePage(SharePageRequest),
    MmioLoad(MmioLoadPending),
    MmioStore(MmioStorePending),
    SbiHsmHartStart(),
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
    SbiSrstSystemReset(SbiSrstSystemReset),
}

impl InterHartRequest {
    pub fn into_expose_to_confidential_vm(self) -> ExposeToConfidentialVm {
        match self {
            Self::SbiIpi(_) => ExposeToConfidentialVm::SbiIpi(),
            Self::SbiRemoteFenceI(v) => ExposeToConfidentialVm::SbiRemoteFenceI(v),
            Self::SbiRemoteSfenceVma(v) => ExposeToConfidentialVm::SbiRemoteSfenceVma(v),
            Self::SbiRemoteSfenceVmaAsid(v) => ExposeToConfidentialVm::SbiRemoteSfenceVmaAsid(v),
            Self::SbiRemoteHfenceGvmaVmid(v) => ExposeToConfidentialVm::SbiRemoteHfenceGvmaVmid(v),
            Self::SbiSrstSystemReset(_) => ExposeToConfidentialVm::SbiSrstSystemReset(),
        }
    }

    pub fn is_hart_selected(&self, hart_id: usize) -> bool {
        match self {
            Self::SbiIpi(v) => Self::_is_hart_selected(hart_id, v.hart_mask(), v.hart_mask_base()),
            Self::SbiRemoteFenceI(v) => Self::_is_hart_selected(hart_id, v.hart_mask(), v.hart_mask_base()),
            Self::SbiRemoteSfenceVma(v) => Self::_is_hart_selected(hart_id, v.hart_mask(), v.hart_mask_base()),
            Self::SbiRemoteSfenceVmaAsid(v) => Self::_is_hart_selected(hart_id, v.hart_mask(), v.hart_mask_base()),
            Self::SbiRemoteHfenceGvmaVmid(v) => Self::_is_hart_selected(hart_id, v.hart_mask(), v.hart_mask_base()),
            Self::SbiSrstSystemReset(v) => v.initiating_confidential_hart_id() != hart_id,
        }
    }

    fn _is_hart_selected(hart_id: usize, hart_mask: usize, hart_mask_base: usize) -> bool {
        // according to SBI documentation all harts are selected when the mask_base is of its maximum value
        match hart_mask_base == usize::MAX {
            true => true,
            false => {
                hart_id.checked_sub(hart_mask_base).filter(|id| *id < usize::BITS as usize).is_some_and(|id| hart_mask & (1 << id) != 0)
            }
        }
    }
}
