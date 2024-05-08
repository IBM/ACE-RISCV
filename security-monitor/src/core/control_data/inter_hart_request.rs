// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::shutdown::ShutdownRequest;
use crate::confidential_flow::handlers::symmetrical_multiprocessing::{
    SbiIpi, SbiRemoteFenceI, SbiRemoteHfenceGvmaVmid, SbiRemoteSfenceVma, SbiRemoteSfenceVmaAsid,
};
use crate::core::control_data::ConfidentialHart;

/// Represents a request send from one confidential hart (sender) to another confidential hart (receiver). Both sender and receiver belong
/// to the same confidential VM.
#[derive(Clone)]
pub enum InterHartRequest {
    SbiIpi(SbiIpi),
    SbiRemoteFenceI(SbiRemoteFenceI),
    SbiRemoteSfenceVma(SbiRemoteSfenceVma),
    SbiRemoteSfenceVmaAsid(SbiRemoteSfenceVmaAsid),
    SbiRemoteHfenceGvmaVmid(SbiRemoteHfenceGvmaVmid),
    ShutdownRequest(ShutdownRequest),
}

impl InterHartRequest {
    pub fn is_hart_selected(&self, confidential_hart_id: usize) -> bool {
        match self {
            Self::SbiIpi(v) => v.is_hart_selected(confidential_hart_id),
            Self::SbiRemoteFenceI(v) => v.is_hart_selected(confidential_hart_id),
            Self::SbiRemoteSfenceVma(v) => v.is_hart_selected(confidential_hart_id),
            Self::SbiRemoteSfenceVmaAsid(v) => v.is_hart_selected(confidential_hart_id),
            Self::SbiRemoteHfenceGvmaVmid(v) => v.is_hart_selected(confidential_hart_id),
            Self::ShutdownRequest(v) => v.is_hart_selected(confidential_hart_id),
        }
    }
}

pub trait InterHartRequestExecutable {
    fn execute_on_confidential_hart(&self, confidential_hart: &mut ConfidentialHart);
    fn is_hart_selected(&self, confidential_hart_id: usize) -> bool;
}
