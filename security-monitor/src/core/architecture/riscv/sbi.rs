// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GpRegister, HartState};

#[derive(Debug)]
pub enum SbiExtension {
    Ace(AceExtension),
    Base(BaseExtension),
    Timer(TimerExtension),
    Ipi(IpiExtension),
    Rfence(RfenceExtension),
    Hsm(HsmExtension),
    Srst(SrstExtension),
    Unknown(usize, usize),
}

impl SbiExtension {
    pub fn decode(hart_state: &HartState) -> Self {
        match (hart_state.gpr(GpRegister::a7), hart_state.gpr(GpRegister::a6)) {
            (AceExtension::EXTID, function_id) => Self::Ace(AceExtension::from_function_id(function_id)),
            (BaseExtension::EXTID, function_id) => Self::Base(BaseExtension::from_function_id(function_id)),
            (TimerExtension::EXTID, function_id) => Self::Timer(TimerExtension::from_function_id(function_id)),
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
    ConvertToConfidentialVm,
    ResumeConfidentialHart,
    TerminateConfidentialVm,
    Unknown(usize, usize),
}

impl AceExtension {
    // TODO: replace with an identifier registered in the RISC-V fundation
    pub const EXTID: usize = 0x510000;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            2000 => Self::SharePageWithHypervisor,
            1000 => Self::ConvertToConfidentialVm,
            1010 => Self::ResumeConfidentialHart,
            3001 => Self::TerminateConfidentialVm,
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
pub enum TimerExtension {
    SetTimer,
    Unknown(usize, usize),
}

impl TimerExtension {
    pub const EXTID: usize = 0x54494D45;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            0 => Self::SetTimer,
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

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            0 => Self::SystemReset,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}
