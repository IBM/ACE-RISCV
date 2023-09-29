// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::transformations::{ExposeToConfidentialVm, ExposeToHypervisor, SbiResult};
use core::num::TryFromIntError;
use fdt_rs::error::DevTreeError;
use thiserror_no_std::Error;

pub const CTX_SWITCH_ERROR_MSG: &str =
    "Invalid assembly implementation of the context switch. a0 must point to the correct processor state";

pub const NOT_INITIALIZED_HART: &str = "Physical hart does not have a state allocated in the confidential memory. There is an error in the security monitor initialization vector";

pub const NOT_INITIALIZED_HARTS: &str =
    "Bug. Could not set mscratch before initializing memory region for HARTs states";

pub const NOT_INITIALIZED_CONTROL_DATA: &str =
    "Bug. Could not access the control data static variable because it is not initialized";

pub const NOT_INITIALIZED_MEMORY_TRACKER: &str =
    "Bug. Could not access memory tracker because it is not initialized";
pub const NOT_INITIALIZED_CONFIDENTIAL_MEMORY: &str =
    "Bug. Could not access confidential memory start/end addresses because they were not initialized";

#[derive(Error, Debug)]
pub enum Error {
    #[error("security monitor initialization error")]
    InitializationError(InitializationErrorType),
    #[error("FDT parsing error")]
    FdtParsing(#[from] DevTreeError),
    #[error("Could not convert SBI argument to usize: {0}")]
    SbiArgument(#[from] TryFromIntError),
    #[error("Not enough memory to allocate")]
    OutOfMemory(),
    #[error("Could not get lock access to a share object")]
    OptimisticLocking(),
    #[error("Page table error")]
    PageTableConfiguration(),
    #[error("Page Table is corrupted")]
    PageTableCorrupted(),
    #[error("Reached a maximum number of CVMs")]
    ReachedMaximumNumberOfCvms(),
    #[error("Unsupported paging mode")]
    UnsupportedPagingMode(),
    #[error("Memory access not authorized")]
    MemoryAccessAuthorization(),
    #[error("There is a pending request")]
    PendingRequest(),
    #[error("Invalid Hart ID")]
    InvalidHartId(),
    #[error("Invalid confidential VM ID")]
    InvalidConfidentialVmId(),
    #[error("vHart is running")]
    RunningVHart(),
    #[error("Invalid riscv instruction: {0:x}")]
    InvalidRiscvInstruction(usize),
    #[error("Not supported interrupt")]
    NotSupportedInterrupt(),
    #[error("Invalid call cause: {0}, extid: {1:x}, fid: {2:x}")]
    InvalidCall(usize, usize, usize),
}

impl Error {
    pub fn into_non_confidential_transformation(self) -> ExposeToHypervisor {
        let error_code = 0x1000;
        ExposeToHypervisor::SbiResult(SbiResult::failure(error_code))
    }

    pub fn into_confidential_transformation(self) -> ExposeToConfidentialVm {
        let error_code = 0x1000;
        ExposeToConfidentialVm::SbiResult(SbiResult::failure(error_code))
    }
}

#[derive(Error, Debug)]
pub enum InitializationErrorType {
    #[error("FDT's memory node not found")]
    FdtMemory,
    #[error("regions of the FDT's memory node not found")]
    FdtMemoryReg,
    #[error("invalid FDT's type casting")]
    FdtMemoryCasting,
    #[error("Too little memory")]
    NotEnoughMemory,
    #[error("Invalid memory boundaries")]
    InvalidMemoryBoundaries,
    #[error("Invalid assembly address")]
    InvalidAssemblyAddress,
}
