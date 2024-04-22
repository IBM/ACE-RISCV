// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![allow(unused)]

#[derive(Debug)]
pub enum SbiExtension {
    Ace(AceExtension),
    Base(BaseExtension),
    Ipi(IpiExtension),
    Rfence(RfenceExtension),
    Hsm(HsmExtension),
    Srst(SrstExtension),
    Nacl(NaclExtension),
    Unknown(usize, usize),
}

impl SbiExtension {
    pub fn decode(a7: usize, a6: usize) -> Self {
        match (a7, a6) {
            (AceExtension::EXTID, function_id) => Self::Ace(AceExtension::from_function_id(function_id)),
            (BaseExtension::EXTID, function_id) => Self::Base(BaseExtension::from_function_id(function_id)),
            (IpiExtension::EXTID, function_id) => Self::Ipi(IpiExtension::from_function_id(function_id)),
            (RfenceExtension::EXTID, function_id) => Self::Rfence(RfenceExtension::from_function_id(function_id)),
            (HsmExtension::EXTID, function_id) => Self::Hsm(HsmExtension::from_function_id(function_id)),
            (SrstExtension::EXTID, function_id) => Self::Srst(SrstExtension::from_function_id(function_id)),
            (extension_id, function_id) => Self::Unknown(extension_id, function_id),
        }
    }
}

#[derive(Debug)]
pub enum AceExtension {
    SharePageWithHypervisor,
    UnsharePageWithHypervisor,
    PromoteVm,
    ResumeConfidentialHart,
    TerminateConfidentialVm,
    PrintDebugInfo,
    Unknown(usize, usize),
}

impl AceExtension {
    // TODO: replace with an identifier registered in the RISC-V fundation
    pub const EXTID: usize = 0x510000;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            1000 => Self::PromoteVm,
            1010 => Self::ResumeConfidentialHart,
            2000 => Self::SharePageWithHypervisor,
            2001 => Self::UnsharePageWithHypervisor,
            3001 => Self::TerminateConfidentialVm,
            9000 => Self::PrintDebugInfo,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}

#[derive(Debug)]
pub enum BaseExtension {
    GetSpecVersion,
    GetImplId,
    GetImplVersion,
    ProbeExtension,
    GetMvendorId,
    GetMarchid,
    GetMimpid,
    Unknown(usize, usize),
}

impl BaseExtension {
    pub const EXTID: usize = 0x10;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            0 => Self::GetSpecVersion,
            1 => Self::GetImplId,
            2 => Self::GetImplVersion,
            3 => Self::ProbeExtension,
            4 => Self::GetMvendorId,
            5 => Self::GetMarchid,
            6 => Self::GetMimpid,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}

#[derive(Debug)]
pub enum IpiExtension {
    SendIpi,
    Unknown(usize, usize),
}

impl IpiExtension {
    pub const EXTID: usize = 0x735049;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            0 => Self::SendIpi,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}

#[derive(Debug)]
pub enum RfenceExtension {
    RemoteFenceI,
    RemoteSfenceVma,
    RemoteSfenceVmaAsid,
    RemoteHfenceGvmaVmid,
    RemoteHfenceGvma,
    RemoteHfenceVvmaAsid,
    RemoteHfenceVvma,
    Unknown(usize, usize),
}

impl RfenceExtension {
    pub const EXTID: usize = 0x52464E43;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            0 => Self::RemoteFenceI,
            1 => Self::RemoteSfenceVma,
            2 => Self::RemoteSfenceVmaAsid,
            3 => Self::RemoteHfenceGvmaVmid,
            4 => Self::RemoteHfenceGvma,
            5 => Self::RemoteHfenceVvmaAsid,
            6 => Self::RemoteHfenceVvma,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}

#[derive(Debug)]
pub enum HsmExtension {
    HartStart,
    HartStop,
    HartGetStatus,
    HartSuspend,
    Unknown(usize, usize),
}

impl HsmExtension {
    pub const EXTID: usize = 0x48534D;
    pub const HART_START_FID: usize = 0x0;
    pub const HART_STOP_FID: usize = 0x1;
    pub const HART_STATUS_FID: usize = 0x2;
    pub const HART_SUSPEND_FID: usize = 0x3;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            Self::HART_START_FID => Self::HartStart,
            Self::HART_STOP_FID => Self::HartStop,
            Self::HART_STATUS_FID => Self::HartGetStatus,
            Self::HART_SUSPEND_FID => Self::HartSuspend,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}

#[derive(Debug)]
pub enum SrstExtension {
    SystemReset,
    Unknown(usize, usize),
}

impl SrstExtension {
    pub const EXTID: usize = 0x53525354;
    pub const SYSTEM_RESET_FID: usize = 0x0;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            Self::SYSTEM_RESET_FID => Self::SystemReset,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}

#[derive(Debug)]
pub enum NaclExtension {
    ProbeFeature,
    SetSharedMemory,
    Unknown(usize, usize),
}

impl NaclExtension {
    pub const EXTID: usize = 0x4E41434C;
    pub const PROBE_FEATURE_FID: usize = 0x0;
    pub const SET_SHARED_MEMORY_FID: usize = 0x1;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            Self::PROBE_FEATURE_FID => Self::ProbeFeature,
            Self::SET_SHARED_MEMORY_FID => Self::SetSharedMemory,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}
