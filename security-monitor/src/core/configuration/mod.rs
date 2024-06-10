// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::specification::*;
use crate::core::architecture::IsaExtension;
use crate::error::Error;
use alloc::vec::Vec;
use spin::{Once, RwLock, RwLockReadGuard, RwLockWriteGuard};

static CONFIGURATION: Once<RwLock<Configuration>> = Once::new();

pub struct Configuration {
    isa_extensions: Vec<IsaExtension>,
}

impl Configuration {
    const NOT_INITIALIZED: &'static str = "Bug: Configuration not initialized";
    const REQUIRED_BASE_EXTENSIONS: &'static [&'static str] = &[ATOMIC_EXTENSION, HYPERVISOR_EXTENSION];
    const REQUIRED_EXTENSIONS: &'static [&'static str] = &[SSTC_EXTENSION, IFENCEI_EXTENSION];

    pub fn initialize() -> Result<(), Error> {
        let configuration = Self { isa_extensions: Vec::new() };
        ensure_not!(CONFIGURATION.is_completed(), Error::Reinitialization())?;
        CONFIGURATION.call_once(|| RwLock::new(configuration));
        Ok(())
    }

    pub fn check_isa_extensions(prop: &str) -> Result<(), Error> {
        // example prop value rv64imafdch_zicsr_zifencei_zba_zbb_zbc_zbs
        ensure!(prop.starts_with(RISCV_ARCH), Error::InvalidCpuArch())?;
        let extensions = &prop.split('_').collect::<Vec<&str>>();

        Self::REQUIRED_BASE_EXTENSIONS
            .into_iter()
            .try_for_each(|ext| ensure!(extensions[0].contains(*ext), Error::MissingCpuExtension()))?;
        Self::REQUIRED_EXTENSIONS.into_iter().try_for_each(|ext| ensure!(extensions.contains(ext), Error::MissingCpuExtension()))?;

        Ok(())
    }

    pub fn add_extension(extension: IsaExtension) -> Result<(), Error> {
        Self::try_write(|configuration| Ok(configuration.isa_extensions.push(extension)))
    }

    pub fn is_extension_supported(extension: IsaExtension) -> bool {
        Self::try_read(|configuration| Ok(configuration.isa_extensions.contains(&extension))).unwrap_or(false)
    }

    fn try_read<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&RwLockReadGuard<'_, Configuration>) -> Result<F, Error> {
        op(&CONFIGURATION.get().expect(Self::NOT_INITIALIZED).read())
    }

    fn try_write<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&mut RwLockWriteGuard<'static, Configuration>) -> Result<F, Error> {
        op(&mut CONFIGURATION.get().expect(Self::NOT_INITIALIZED).write())
    }
}
