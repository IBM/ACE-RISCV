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
    Cove(CoveExtension),
    Covg(CovgExtension),
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
            (NaclExtension::EXTID, function_id) => Self::Nacl(NaclExtension::from_function_id(function_id)),
            (CoveExtension::EXTID, function_id) => Self::Cove(CoveExtension::from_function_id(function_id)),
            (CovgExtension::EXTID, function_id) => Self::Covg(CovgExtension::from_function_id(function_id)),
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
    SetupSharedMemory,
    Unknown(usize, usize),
}

impl NaclExtension {
    pub const EXTID: usize = 0x4E41434C;
    pub const SBI_EXT_NACL_PROBE_FEATURE: usize = 0x0;
    pub const SBI_EXT_NACL_SETUP_SHMEM: usize = 0x1;
    pub const SBI_EXT_NACL_SYNC_CSR: usize = 0x2;
    pub const SBI_EXT_NACL_SYNC_HFENCE: usize = 0x3;
    pub const SBI_EXT_NACL_SYNC_SRET: usize = 0x4;

    pub const SBI_NACL_FEAT_SYNC_CSR: usize = 0;
    pub const SBI_NACL_FEAT_SYNC_HFENCE: usize = 1;
    pub const SBI_NACL_FEAT_SYNC_SRET: usize = 2;
    pub const SBI_NACL_FEAT_AUTOSWAP_CSR: usize = 3;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            Self::SBI_EXT_NACL_PROBE_FEATURE => Self::ProbeFeature,
            Self::SBI_EXT_NACL_SETUP_SHMEM => Self::SetupSharedMemory,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}

#[derive(Debug)]
pub enum CoveExtension {
    TsmGetInfo,
    PromoteToTvm,
    DestroyTvm,
    TvmVcpuRun,
    Unknown(usize, usize),
}

impl CoveExtension {
    pub const EXTID: usize = 0x434F5648;
    pub const SBI_EXT_COVH_TSM_GET_INFO: usize = 0;
    pub const SBI_EXT_COVH_TSM_CONVERT_PAGES: usize = 1;
    pub const SBI_EXT_COVH_TSM_RECLAIM_PAGES: usize = 2;
    pub const SBI_EXT_COVH_TSM_INITIATE_FENCE: usize = 3;
    pub const SBI_EXT_COVH_TSM_LOCAL_FENCE: usize = 4;
    pub const SBI_EXT_COVH_CREATE_TVM: usize = 5;
    pub const SBI_EXT_COVH_FINALIZE_TVM: usize = 6;
    pub const SBI_EXT_COVH_DESTROY_TVM: usize = 7;
    pub const SBI_EXT_COVH_TVM_ADD_MEMORY_REGION: usize = 8;
    pub const SBI_EXT_COVH_TVM_ADD_PGT_PAGES: usize = 9;
    pub const SBI_EXT_COVH_TVM_ADD_MEASURED_PAGES: usize = 10;
    pub const SBI_EXT_COVH_TVM_ADD_ZERO_PAGES: usize = 11;
    pub const SBI_EXT_COVH_TVM_ADD_SHARED_PAGES: usize = 12;
    pub const SBI_EXT_COVH_TVM_CREATE_VCPU: usize = 13;
    pub const SBI_EXT_COVH_TVM_VCPU_RUN: usize = 14;
    pub const SBI_EXT_COVH_TVM_INITIATE_FENCE: usize = 15;
    pub const SBI_EXT_COVH_TVM_INVALIDATE_PAGES: usize = 16;
    pub const SBI_EXT_COVH_TVM_VALIDATE_PAGES: usize = 17;
    pub const SBI_EXT_COVH_TVM_PROMOTE_PAGE: usize = 18;
    pub const SBI_EXT_COVH_TVM_DEMOTE_PAGE: usize = 19;
    pub const SBI_EXT_COVH_TVM_REMOVE_PAGES: usize = 20;
    pub const SBI_EXT_COVH_PROMOTE_TO_TVM: usize = 21;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            Self::SBI_EXT_COVH_TSM_GET_INFO => Self::TsmGetInfo,
            Self::SBI_EXT_COVH_DESTROY_TVM => Self::DestroyTvm,
            Self::SBI_EXT_COVH_TVM_VCPU_RUN => Self::TvmVcpuRun,
            Self::SBI_EXT_COVH_PROMOTE_TO_TVM => Self::PromoteToTvm,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}

#[derive(Debug)]
pub enum CovgExtension {
    Unknown(usize, usize),
}

impl CovgExtension {
    pub const EXTID: usize = 0x434F5647;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}
