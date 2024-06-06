// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::shutdown::ShutdownRequest;
use crate::confidential_flow::handlers::symmetrical_multiprocessing::{
    Ipi, RemoteFenceI, RemoteHfenceGvmaVmid, RemoteSfenceVma, RemoteSfenceVmaAsid,
};
use crate::core::control_data::ConfidentialHart;

/// Represents a command that must be executed on a confidential hart. Typically this is an inter hart request that was sent from one
/// confidential hart (sender) to another confidential hart (receiver), both sender and receiver belong to the same confidential VM.
/// However, there might also be commands that are originating from the hypervisor (e.g., injection of an external interrupt). All these
/// command preserve the same semantics: they originate from the outside of the hart, the receiver might be currently running or not. If the
/// receiver hart is running, it is interrupted (IPI) and executes the command. If the hart is not running, the command is buffered and
/// executed on the next time the receiver is scheduled to run.
#[derive(Clone)]
pub enum ConfidentialHartRemoteCommand {
    Ipi(Ipi),
    RemoteFenceI(RemoteFenceI),
    RemoteSfenceVma(RemoteSfenceVma),
    RemoteSfenceVmaAsid(RemoteSfenceVmaAsid),
    RemoteHfenceGvmaVmid(RemoteHfenceGvmaVmid),
    ShutdownRequest(ShutdownRequest),
}

impl ConfidentialHartRemoteCommand {
    pub fn is_hart_selected(&self, confidential_hart_id: usize) -> bool {
        match self {
            Self::Ipi(v) => v.is_hart_selected(confidential_hart_id),
            Self::RemoteFenceI(v) => v.is_hart_selected(confidential_hart_id),
            Self::RemoteSfenceVma(v) => v.is_hart_selected(confidential_hart_id),
            Self::RemoteSfenceVmaAsid(v) => v.is_hart_selected(confidential_hart_id),
            Self::RemoteHfenceGvmaVmid(v) => v.is_hart_selected(confidential_hart_id),
            Self::ShutdownRequest(v) => v.is_hart_selected(confidential_hart_id),
        }
    }
}

pub trait ConfidentialHartRemoteCommandExecutable {
    fn execute_on_confidential_hart(&self, confidential_hart: &mut ConfidentialHart);
    fn is_hart_selected(&self, confidential_hart_id: usize) -> bool;
}
