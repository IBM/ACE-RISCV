// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(Debug)]
pub enum CovhExtension {
    TsmGetInfo,
    PromoteToTvm,
    DestroyTvm,
    TvmVcpuRun,
    Unknown(usize, usize),
}

impl CovhExtension {
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

/// State of the security monitor communicated to the hypervisor. This structure is defined in CoVE specification.
#[repr(u32)]
pub enum SecurityMonitorState {
    NotLoaded = 0,
    Loaded = 1,
    Ready = 2,
}

/// Information written by the security monitor to the hypervisor memory, representing the state of the security monitor. This structure is
/// defined in CoVE specification.
#[repr(C)]
pub struct SecurityMonitorInfo {
    pub security_monitor_state: SecurityMonitorState,
    pub security_monitor_version: u32,
    pub state_pages: u64,
    pub max_vcpus: u64,
    pub vcpu_state_pages: u64,
}
