// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::{SbiRequest, SbiResponse};
use crate::non_confidential_flow::handlers::delegate_to_opensbi::OpensbiHandler;
use crate::non_confidential_flow::handlers::promote_vm::PromoteVmHandler;

/// Transformation of the hypervisor state created as a result of processing a hypervisor call.
pub enum ApplyToHypervisor {
    PromoteVmResponse(PromoteVmHandler),
    SbiRequest(SbiRequest),
    SbiResponse(SbiResponse),
    OpenSbiResponse(OpensbiHandler),
}
