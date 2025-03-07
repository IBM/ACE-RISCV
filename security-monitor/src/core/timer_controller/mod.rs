use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::specification::*;
use crate::core::architecture::CSR;

extern "C" {
    fn sbi_timer_value() -> u64;
}

pub struct TimerController<'a, 'b> {
    current_time: usize,
    confidential_flow: &'a mut ConfidentialFlow<'b>,
}

impl<'a, 'b> TimerController<'a, 'b> {
    pub fn new(confidential_flow: &'a mut ConfidentialFlow<'b>) -> Self {
        Self { current_time: TimerController::read_time(), confidential_flow }
    }

    pub fn read_time() -> usize {
        unsafe { (0x200BFF8 as *const usize).read_volatile() }
    }

    pub fn read_virt_time(htimedelta: usize) -> usize {
        TimerController::read_time().wrapping_add(htimedelta)
    }

    pub fn set_next_event_for_vs_mode(&mut self, next_event: usize) {
        if next_event >= usize::MAX - 1 {
            self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp = None;
        } else {
            let htimedelta = self.confidential_flow.confidential_hart_mut().csrs_mut().htimedelta;
            let next_event = (next_event as isize).wrapping_sub(htimedelta as isize) as usize;
            self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp = Some(next_event);
            if self.vs_timer_interrupted() {
                self.handle_vs_interrupt();
                self.set_s_timer();
            } else if self.should_set_vs_timer() {
                self.set_vs_timer();
            } else {
                self.set_s_timer();
                self.confidential_flow.confidential_hart_mut().csrs_mut().pending_interrupts &= !MIE_VSTIP_MASK;
                self.confidential_flow.confidential_hart_mut().csrs_mut().mip.read_and_clear_bits(MIE_MTIP_MASK);
            }
        }
    }

    fn should_set_vs_timer(&mut self) -> bool {
        let stimecmp = self.confidential_flow.confidential_hart_mut().csrs_mut().stimecmp;
        self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp.and_then(|v| Some(v <= stimecmp)).unwrap_or(false)
    }

    pub fn s_timer_interrupted(&mut self) -> bool {
        self.current_time >= self.confidential_flow.confidential_hart_mut().csrs_mut().stimecmp
    }

    pub fn vs_timer_interrupted(&mut self) -> bool {
        self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp.and_then(|v| Some(self.current_time >= v)).unwrap_or(false)
    }

    pub fn handle_vs_interrupt(&mut self) {
        self.confidential_flow.confidential_hart_mut().csrs_mut().pending_interrupts |= MIE_VSTIP_MASK;
        self.confidential_flow.confidential_hart_mut().csrs_mut().mip.read_and_clear_bits(MIE_MTIP_MASK);
    }

    pub fn store_vs_timer(&mut self) {
        if self.vs_timer_interrupted() {
            self.handle_vs_interrupt();
        }

        // if let Some(v) = self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp {
        //     let cycles_left = if v > self.current_time { v - self.current_time } else { 0 };
        //     self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp = Some(cycles_left);
        // }

        self.set_s_timer();
    }

    pub fn restore_vs_timer(&mut self) {
        let mut mtimecmp = self.read_mtimecmp();
        // if mtimecmp == usize::MAX {
        //     mtimecmp = self.current_time + 10000;
        // }
        self.confidential_flow.confidential_hart_mut().csrs_mut().stimecmp = mtimecmp;

        if let Some(v) = self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp {
            // self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp = self.current_time.checked_add(v);

            if self.vs_timer_interrupted() {
                self.handle_vs_interrupt();
                self.set_s_timer();
            } else if self.should_set_vs_timer() {
                self.set_vs_timer();
            } else {
                self.set_s_timer();
            }
        } else {
            self.set_s_timer();
        }
    }

    fn read_mtimecmp(&mut self) -> usize {
        let addr = 0x2004000 + CSR.mhartid.read() * 8;
        unsafe { (addr as *const usize).read_volatile() }
    }

    pub fn set_s_timer(&mut self) {
        let next_event = self.confidential_flow.confidential_hart_mut().csrs_mut().stimecmp;
        self.set_m_timer(next_event);
        self.confidential_flow.confidential_hart_mut().csrs_mut().mip.read_and_clear_bits(MIE_MTIP_MASK);
    }

    fn set_vs_timer(&mut self) {
        if let Some(next_event) = self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp {
            self.set_m_timer(next_event);
            self.confidential_flow.confidential_hart_mut().csrs_mut().pending_interrupts &= !MIE_VSTIP_MASK;
            self.confidential_flow.confidential_hart_mut().csrs_mut().mip.read_and_clear_bits(MIE_MTIP_MASK);
        }
    }

    fn set_m_timer(&mut self, next_event: usize) {
        let addr = 0x2004000 + CSR.mhartid.read() * 8;
        unsafe { (addr as *mut usize).write_volatile(next_event) };
    }
}
