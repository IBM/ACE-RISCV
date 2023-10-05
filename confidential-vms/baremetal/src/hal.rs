// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use core::{ptr::NonNull, sync::atomic::Ordering};
use virtio_drivers::PAGE_SIZE;
use virtio_drivers::{BufferDirection, Hal, PhysAddr};

pub struct ScratchPage {
    pub base_paddr: usize,
    pub position: usize,
    pub translations: alloc::vec::Vec<BufferTranslation>,
}

pub struct BufferTranslation {
    pub vaddr: usize,
    pub paddr: usize,
    pub position: usize,
    pub len: usize,
}

pub struct HalSvmImpl {}

unsafe impl Hal for HalSvmImpl {
    fn dma_alloc(pages: usize, _direction: BufferDirection) -> (PhysAddr, NonNull<u8>) {
        let paddr = unsafe {
            if let Some(v) = &crate::DMA_PADDR {
                v.fetch_add(PAGE_SIZE * pages, Ordering::SeqCst)
            } else {
                panic!("DMA_PADDR not initialized");
            }
        };
        for i in 0..pages {
            crate::calls::sm::share_page(paddr + i * 4096, 1).expect("DMA alloc failed");
        }
        let vaddr = NonNull::new(paddr as _).unwrap();

        (paddr, vaddr)
    }

    unsafe fn dma_dealloc(_paddr: PhysAddr, _vaddr: NonNull<u8>, _pages: usize) -> i32 {
        // TODO: implement
        0
    }

    unsafe fn mmio_phys_to_virt(paddr: PhysAddr, _size: usize) -> NonNull<u8> {
        NonNull::new(paddr as _).unwrap()
    }

    unsafe fn share(buffer: NonNull<[u8]>, _direction: BufferDirection) -> PhysAddr {
        let vaddr = buffer.as_ptr() as *mut u8 as usize;

        if vaddr >= crate::_dma_start as usize && vaddr < crate::_dma_end as usize {
            // println!("share {:x} -> {:x}", vaddr, vaddr);
            return vaddr;
        }

        let paddr = unsafe {
            crate::SCRATCH_PAGE
                .as_mut()
                .and_then(|sp| {
                    let position = sp.position;
                    let paddr = sp.base_paddr + position;
                    sp.translations.push(BufferTranslation {
                        vaddr,
                        paddr,
                        position,
                        len: buffer.len(),
                    });
                    for i in 0..buffer.len() {
                        let input_ptr = (vaddr + i) as *mut u8;
                        let output_ptr = (sp.base_paddr + sp.position) as *mut u8;
                        let value = input_ptr.read_volatile();
                        output_ptr.write_volatile(value);
                        sp.position += 1;
                    }
                    Some(paddr)
                })
                .unwrap()
        };

        // println!("share {:x} -> {:x} (buffer len: {})", vaddr, paddr, buffer.len());
        paddr
    }

    unsafe fn unshare(paddr: PhysAddr, _buffer: NonNull<[u8]>, _direction: BufferDirection) {
        unsafe {
            if let Some(sp) = crate::SCRATCH_PAGE.as_mut() {
                let mut index_to_remove = None;
                for (i, x) in sp.translations.iter().enumerate() {
                    if x.paddr == paddr {
                        index_to_remove = Some(i);
                        // write back to the confidential memory
                        for _ in 0..x.len {
                            let input_ptr = (paddr + i) as *mut u8;
                            let output_ptr = (x.vaddr + i) as *mut u8;
                            let value = input_ptr.read_volatile();
                            output_ptr.write_volatile(value);
                        }
                    }
                }
                if let Some(i) = index_to_remove {
                    sp.translations.remove(i);
                }
            };
        }
    }
}
