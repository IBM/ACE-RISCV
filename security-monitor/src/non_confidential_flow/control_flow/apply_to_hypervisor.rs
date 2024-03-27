// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::{SbiRequest, SbiResult};
use crate::non_confidential_flow::handlers::delegate_hypercall::SbiVmRequest;
use crate::non_confidential_flow::handlers::delegate_to_opensbi::OpensbiResult;

/// Transformation that modifies hypervisor state as a result of processing its own request
pub enum ApplyToHypervisor {
    SbiRequest(SbiRequest),
    SbiResult(SbiResult),
    SbiVmRequest(SbiVmRequest),
    OpensbiResult(OpensbiResult),
    Nothing(),
}
