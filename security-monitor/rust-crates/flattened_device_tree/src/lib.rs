// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![no_std]
#![no_main]

use fdt_rs::base::DevTree;
use fdt_rs::prelude::{FallibleIterator, PropReader};
use fdt_rs::base::DevTreeNode;
use crate::FdtError::FdtPointerNotAligned;
use core::mem::align_of;

pub use crate::error::FdtError;

mod error;

/// This is a wrapper over a third party library that parses the flattened device tree (FDT).
pub struct FlattenedDeviceTree<'a> {
    inner: DevTree<'a>
}

impl<'a> FlattenedDeviceTree<'a> {
    /// Creates an instance of a wrapper over the library that parses the flattened device tree (FDT). Returns error if address is not a 4-bytes aligned pointer to the valid flattened device tree (FDT).
    ///
    /// # Safety
    ///
    /// Caller must guarantee that:
    ///   * the length of the pointed buffer is at least `DevTree::MIN_HEADER_SIZE`
    pub unsafe fn from_raw_pointer(address: *const u8) -> Result<Self, FdtError> {
        if address.align_offset(align_of::<u32>()) != 0 {
            return Err(FdtPointerNotAligned());
        }
        Ok(Self { inner: unsafe { DevTree::from_raw_pointer(address)? } })
    }

    pub fn harts<'b>(&'b self) -> impl Iterator<Item = Hart<'b, 'a>> {
        self.inner
            .nodes()
            .filter(|n| {
                n.props()
                    .any(|p| Ok(p.name()? == "device_type" && p.str()? == "cpu"))
            })
            .iterator()
            .filter_map(|n| Some(Hart { inner: n.ok()? }))
    }

    pub fn memory(&self) -> Result<FdtMemoryRegion, FdtError>  {
        let mem_prop = self.inner.props()
            .find(|p| Ok(p.name()? == "device_type" && p.str()? == "memory"))?
            .ok_or_else(|| FdtError::NoMemoryNode())?;

        let reg_prop = mem_prop.node()
            .props()
            .find(|p| Ok(p.name().unwrap_or("empty") == "reg"))?
            .ok_or_else(|| FdtError::NoMemoryNode())?;

        Ok(FdtMemoryRegion { base: reg_prop.u64(0)?, size: reg_prop.u64(1)? })
    }
}

#[derive(Copy, Clone, Debug, Default)]
pub struct FdtMemoryRegion {
    pub base: u64,
    pub size: u64,
}

#[derive(Clone)]
pub struct Hart<'a, 'dt> {
    inner: DevTreeNode<'a, 'dt>,
}

impl<'a, 'dt> Hart<'a, 'dt> {
    pub fn hart_id(&self) -> Option<u64> {
        let prop = self.inner.props().find(|p| Ok(p.name()? == "reg")).ok()??;
        Some(prop.u32(0).ok()? as u64)
    }

    pub fn property_str(&self, name: &str) -> Option<&str> {
        let prop = self.inner.props().find(|p| Ok(p.name()? == name)).ok()??;
        let value = core::str::from_utf8(prop.propbuf()).ok().and_then(|v| v.strip_suffix('\0'))?;
        Some(value)
    }

}