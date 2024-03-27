// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::shutdown::ShutdownRequest;
use crate::confidential_flow::handlers::smp::{
    SbiIpi, SbiRemoteFenceI, SbiRemoteHfenceGvmaVmid, SbiRemoteSfenceVma, SbiRemoteSfenceVmaAsid,
};

/// Represents a request send from one confidential hart (sender) to another confidential hart (receiver). Both sender and receiver belong
/// to the same confidential VM.
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
            Self::ShutdownRequest(v) => v.is_hart_selected(hart_id),
        }
    }
}
