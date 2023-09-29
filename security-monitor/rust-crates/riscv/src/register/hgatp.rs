//! hgatp register

#[repr(usize)]
#[derive(Clone, Copy, Debug)]
pub enum HgatpMode {
    Sv57x4 = 10
}

impl HgatpMode {
    fn code(self) -> usize {
        self as usize
    }

    fn from_code(code: usize) -> Option<Self> {
        match code {
            10 => Some(HgatpMode::Sv57x4),
            _ => None,
        }
    }
}


/// sie register
#[derive(Clone, Copy, Debug)]
pub struct Hgatp {
    bits: usize,
}

impl Hgatp {
    const HGATP64_MODE_SHIFT: usize = 60;
    const HGATP64_VMID_SHIFT: usize = 44;
    const PAGE_SHIFT: usize = 12;
    const HGATP_PPN_MASK: usize = 0x0000FFFFFFFFFFF;
    const VMID_MASK: usize = 0x3fff;

    pub fn from(bits: usize) -> Self {
        Self {
            bits
        }
    }

    /// Returns the contents of the register as raw bits
    #[inline]
    pub fn bits(&self) -> usize {
        self.bits
    }

    #[inline]
    pub fn vmid(&self) -> usize {
        (self.bits >> Self::HGATP64_VMID_SHIFT) & Self::VMID_MASK
    }

    pub fn address(&self) -> usize {
        (self.bits & Self::HGATP_PPN_MASK) << Self::PAGE_SHIFT
    }    

    pub fn mode(&self) -> Option<HgatpMode> {
        HgatpMode::from_code((self.bits >> Self::HGATP64_MODE_SHIFT) & 0b1111)
    }    

    pub fn new(address: usize, mode: HgatpMode, vmid: usize) -> Self {
        let ppn = (address >> Self::PAGE_SHIFT) & Self::HGATP_PPN_MASK;
        Self {
            bits: (vmid << Self::HGATP64_VMID_SHIFT) | (mode.code() << Self::HGATP64_MODE_SHIFT) | ppn
        }
    }    
}

read_csr_as!(Hgatp, 0x680);
set!(0x680);
clear!(0x680);

write_csr!(0x680);

/// Writes the CSR
#[inline]
pub unsafe fn write(bits: usize) {
    _write(bits);
}
