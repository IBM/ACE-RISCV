// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::hal::HalSvmImpl;
use core::ptr::NonNull;
use fdt::node::FdtNode;
use fdt::Fdt;
use virtio_drivers::device::blk::VirtIOBlk;
use virtio_drivers::transport::mmio::VirtIOHeader;
use virtio_drivers::transport::{mmio::MmioTransport, DeviceType, Transport};

pub fn get_block_device(dtb: usize) -> Option<VirtIOBlk<HalSvmImpl, MmioTransport>> {
    let transport = get_transport(dtb).expect("blk device not found");
    Some(
        VirtIOBlk::<HalSvmImpl, MmioTransport>::new(transport)
            .expect("failed to create blk driver"),
    )
}

pub fn get_transport(dtb: usize) -> Option<MmioTransport> {
    let fdt = unsafe { Fdt::from_ptr(dtb as *const u8).expect("Failed to open FDT") };
    for node in fdt.all_nodes() {
        if let Some(compatible) = node.compatible() {
            if compatible.all().any(|s| s == "virtio,mmio") {
                return virtio_probe(node);
            }
        }
    }
    None
}

fn virtio_probe(node: FdtNode) -> Option<MmioTransport> {
    if let Some(reg) = node.reg().and_then(|mut reg| reg.next()) {
        let paddr = reg.starting_address as usize;
        let _size = reg.size.unwrap();
        let vaddr = paddr;
        if let Some(header) = NonNull::new(vaddr as *mut VirtIOHeader) {
            if let Ok(transport) = unsafe { MmioTransport::new(header) } {
                if transport.device_type() == DeviceType::Block {
                    return Some(transport);
                }
            }
        }
    }
    None
}
