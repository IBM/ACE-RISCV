// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::shutdown::ShutdownRequest;
use crate::confidential_flow::handlers::symmetrical_multiprocessing::{
    SbiIpi, SbiRemoteFenceI, SbiRemoteHfenceGvmaVmid, SbiRemoteSfenceVma, SbiRemoteSfenceVmaAsid,
};
use crate::core::control_data::ConfidentialHart;
use crate::non_confidential_flow::handlers::covi::InjectExternalInterrupt;

/// Represents a command that must be executed on a confidential hart. Typically this is an inter hart request that was sent from one
/// confidential hart (sender) to another confidential hart (receiver), both sender and receiver belong to the same confidential VM.
/// However, there might also be commands that are originating from the hypervisor (e.g., injection of an external interrupt). All these
/// command preserve the same semantics: they originate from the outside of the hart, the receiver might be currently running or not. If the
/// receiver hart is running, it is interrupted (IPI) and executes the command. If the hart is not running, the command is buffered and
/// executed on the next time the receiver is scheduled to run.
#[derive(Clone)]
pub enum ConfidentialHartRemoteCommand {
    SbiIpi(SbiIpi),
    SbiRemoteFenceI(SbiRemoteFenceI),
    SbiRemoteSfenceVma(SbiRemoteSfenceVma),
    SbiRemoteSfenceVmaAsid(SbiRemoteSfenceVmaAsid),
    SbiRemoteHfenceGvmaVmid(SbiRemoteHfenceGvmaVmid),
    ShutdownRequest(ShutdownRequest),
    ExternalInterrupt(InjectExternalInterrupt),
}

impl ConfidentialHartRemoteCommand {
    pub fn is_hart_selected(&self, confidential_hart_id: usize) -> bool {
        match self {
            Self::SbiIpi(v) => v.is_hart_selected(confidential_hart_id),
            Self::SbiRemoteFenceI(v) => v.is_hart_selected(confidential_hart_id),
            Self::SbiRemoteSfenceVma(v) => v.is_hart_selected(confidential_hart_id),
            Self::SbiRemoteSfenceVmaAsid(v) => v.is_hart_selected(confidential_hart_id),
            Self::SbiRemoteHfenceGvmaVmid(v) => v.is_hart_selected(confidential_hart_id),
            Self::ShutdownRequest(v) => v.is_hart_selected(confidential_hart_id),
            Self::ExternalInterrupt(v) => v.is_hart_selected(confidential_hart_id),
        }
    }
}

pub trait ConfidentialHartRemoteCommandExecutable {
    fn execute_on_confidential_hart(&self, confidential_hart: &mut ConfidentialHart);
    fn is_hart_selected(&self, confidential_hart_id: usize) -> bool;
}