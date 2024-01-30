// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::transformations::{ExposeToConfidentialVm, ExposeToHypervisor, SbiResult};
use core::num::TryFromIntError;
use fdt::FdtError;
use pointers_utility::PointerError;
use thiserror_no_std::Error;

pub const CTX_SWITCH_ERROR_MSG: &str =
    "Invalid assembly implementation of the context switch. a0 must point to the correct processor state";

pub const NOT_INITIALIZED_HART: &str = "Physical hart does not have a state allocated in the confidential memory. There is an error in the security monitor initialization vector";

pub const NOT_INITIALIZED_HARTS: &str = "Bug. Could not set mscratch before initializing memory region for HARTs states";

pub const NOT_INITIALIZED_CONTROL_DATA: &str = "Bug. Could not access the control data static variable because it is not initialized";

#[derive(Error, Debug)]
pub enum Error {
    #[error("security monitor initialization error")]
    Init(InitType),
    #[error("Cannot initialize memory as it has already been initialized")]
    Reinitialization(),
    #[error("Not supported hardware")]
    NotSupportedHardware(HardwareFeatures),
    #[error("FDT read error")]
    FdtFromPtr(#[from] FdtError),
    #[error("Error while searching FDT for a property")]
    FdtParsing(),
    #[error("Could not convert SBI argument to usize: {0}")]
    SbiArgument(#[from] TryFromIntError),
    #[error("Not enough memory to allocate")]
    OutOfMemory(),
    #[error("Page table error")]
    PageTableConfiguration(),
    #[error("Page Table is corrupted")]
    PageTableCorrupted(),
    #[error("Reached a maximum number of confidential VMs")]
    TooManyConfidentialVms(),
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
    HartAlreadyRunning(),
    #[error("Hart is not executable")]
    HartNotExecutable(),
    #[error("Invalid riscv instruction: {0:x}")]
    InvalidRiscvInstruction(usize),
    #[error("Not supported interrupt")]
    NotSupportedInterrupt(),
    #[error("Invalid call cause: {0}")]
    InvalidCall(usize),
    #[error("Internal error")]
    Pointer(#[from] PointerError),
    #[error("Reached max number of remote hart requests")]
    ReachedMaxNumberOfRemoteHartRequests(),
    #[error("Sending interrupt error")]
    InterruptSendingError(),

    // SBI HSM extension related errors
    #[error("Cannot start a confidential hart because it is not in the Stopped state.")]
    CannotStartNotStoppedHart(),
    #[error("Cannot stop a confidential hart because it is not in the Started state.")]
    CannotStopNotStartedHart(),
    #[error("Cannot suspend a confidential hart because it is not in the Started state.")]
    CannotSuspedNotStartedHart(),
    #[error("Cannot start a confidential hart because it is not in the Suspended state.")]
    CannotStartNotSuspendedHart(),
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
pub enum InitType {
    #[error("FDT's memory node not found")]
    FdtMemory,
    #[error("Too little memory")]
    NotEnoughMemory,
    #[error("Invalid memory boundaries")]
    MemoryBoundary,
    #[error("Invalid assembly address")]
    InvalidAssemblyAddress,
}

#[derive(Error, Debug)]
pub enum HardwareFeatures {
    #[error("ACE requires 64-bit processor")]
    InvalidCpuArch,
    #[error("CPU does not support the required ISA extension: {0}")]
    NoCpuExtension(char),
    #[error("Not enough PMPs")]
    NotEnoughPmps,
}
