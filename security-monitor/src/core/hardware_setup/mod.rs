// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::HardwareExtension;
use crate::core::architecture::riscv::specification::*;
use crate::error::Error;
use alloc::vec::Vec;
use spin::{Once, RwLock, RwLockReadGuard, RwLockWriteGuard};

/// Global static description of hardware setup. It is created during the system initiization and used in runtime to perform operations that
/// depend on the presence of specific hardware features, like, for example, floating point unit extension.
static HARDWARE_SETUP: Once<RwLock<HardwareSetup>> = Once::new();

pub struct HardwareSetup {
    isa_extensions: Vec<HardwareExtension>,
}

impl HardwareSetup {
    const NOT_INITIALIZED: &'static str = "Bug: Hardware configuration setup not initialized";
    const REQUIRED_BASE_EXTENSIONS: &'static [&'static str] = &[ATOMIC_EXTENSION, HYPERVISOR_EXTENSION];
    const REQUIRED_EXTENSIONS: &'static [&'static str] = &[SSTC_EXTENSION, IFENCEI_EXTENSION];

    pub fn initialize() -> Result<(), Error> {
        let hardware_setup = Self { isa_extensions: Vec::new() };
        ensure_not!(HARDWARE_SETUP.is_completed(), Error::Reinitialization())?;
        HARDWARE_SETUP.call_once(|| RwLock::new(hardware_setup));
        Ok(())
    }

    pub fn check_isa_extensions(prop: &str) -> Result<(), Error> {
        // example prop value rv64imafdch_zicsr_zifencei_zba_zbb_zbc_zbs
        debug!("{}", prop);
        ensure!(prop.starts_with(RISCV_ARCH), Error::InvalidCpuArch())?;
        let extensions = &prop.split('_').collect::<Vec<&str>>();
        Self::REQUIRED_BASE_EXTENSIONS
            .into_iter()
            .try_for_each(|ext| ensure!(extensions[0].contains(*ext), Error::MissingCpuExtension()))?;
        Self::REQUIRED_EXTENSIONS.into_iter().try_for_each(|ext| ensure!(extensions.contains(ext), Error::MissingCpuExtension()))?;
        Ok(())
    }

    pub fn add_extension(extension: HardwareExtension) -> Result<(), Error> {
        Self::try_write(|hardware_setup| Ok(hardware_setup.isa_extensions.push(extension)))
    }

    pub fn is_extension_supported(extension: HardwareExtension) -> bool {
        Self::try_read(|hardware_setup| Ok(hardware_setup.isa_extensions.contains(&extension))).unwrap_or(false)
    }

    fn try_read<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&RwLockReadGuard<'_, Self>) -> Result<F, Error> {
        op(&HARDWARE_SETUP.get().expect(Self::NOT_INITIALIZED).read())
    }

    fn try_write<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&mut RwLockWriteGuard<'static, Self>) -> Result<F, Error> {
        op(&mut HARDWARE_SETUP.get().expect(Self::NOT_INITIALIZED).write())
    }
}
