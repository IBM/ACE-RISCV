// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use convert_to_confidential_vm_request::ConvertToConfidentialVm;
pub use guest_load_page_fault_request::GuestLoadPageFaultRequest;
pub use guest_load_page_fault_result::GuestLoadPageFaultResult;
pub use guest_store_page_fault_request::GuestStorePageFaultRequest;
pub use guest_store_page_fault_result::GuestStorePageFaultResult;
pub use interrupt_request::InterruptRequest;
pub use mmio_load_request::MmioLoadRequest;
pub use mmio_store_request::MmioStoreRequest;
pub use opensbi_request::OpensbiRequest;
pub use resume_request::ResumeRequest;
pub use sbi_request::SbiRequest;
pub use sbi_result::SbiResult;
pub use sbi_vm_request::SbiVmRequest;
pub use share_page_request::{ConfidentialVmVirtualAddress, SharePageRequest};
pub use share_page_result::SharePageResult;
pub use terminate_request::TerminateRequest;
pub use trap_reason::TrapReason;

mod convert_to_confidential_vm_request;
mod guest_load_page_fault_request;
mod guest_load_page_fault_result;
mod guest_store_page_fault_request;
mod guest_store_page_fault_result;
mod interrupt_request;
mod mmio_load_request;
mod mmio_store_request;
mod opensbi_request;
mod resume_request;
mod sbi_request;
mod sbi_result;
mod sbi_vm_request;
mod share_page_request;
mod share_page_result;
mod terminate_request;
mod trap_reason;

pub enum ExposeToHypervisor {
    SbiRequest(SbiRequest),
    SbiResult(SbiResult),
    SbiVmRequest(SbiVmRequest),
    MmioLoadRequest(MmioLoadRequest),
    MmioStoreRequest(MmioStoreRequest),
    InterruptRequest(InterruptRequest),
}

pub enum ExposeToConfidentialVm {
    SbiResult(SbiResult),
    GuestLoadPageFaultResult(GuestLoadPageFaultResult),
    GuestStorePageFaultResult(GuestStorePageFaultResult),
    Resume(),
}

#[derive(PartialEq)]
pub enum PendingRequest {
    SharePage(SharePageRequest),
    GuestLoadPageFault(GuestLoadPageFaultRequest),
    GuestStorePageFault(GuestStorePageFaultRequest),
    SbiRequest(),
}
