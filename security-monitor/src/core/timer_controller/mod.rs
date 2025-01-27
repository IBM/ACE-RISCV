use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::specification::*;
use crate::core::architecture::CSR;
use crate::core::control_data::ConfidentialHart;
use crate::error::Error;
use spin::{Once, RwLock, RwLockReadGuard, RwLockWriteGuard};

extern "C" {
    fn sbi_timer_event_start(next_event: u64);
    fn sbi_timer_value() -> u64;
}

pub struct TimerController<'a, 'b> {
    current_time: usize,
    confidential_flow: &'a mut ConfidentialFlow<'b>,
}

impl<'a, 'b> TimerController<'a, 'b> {
    pub fn new(confidential_flow: &'a mut ConfidentialFlow<'b>) -> Self {
        Self { current_time: CSR.time.read(), confidential_flow }
    }

    pub fn set_next_event_for_vs_mode(&mut self, next_event: usize) {
        if next_event >= usize::MAX - 1 {
            self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp = None;
        } else {
            self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp = Some(next_event);
            if self.should_set_vs_timer() {
                self.set_vs_timer();
            }
        }
    }

    fn is_vs_timer_programmed(&mut self) -> bool {
        self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp.is_some()
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
    }

    pub fn store_vs_timer(&mut self) {
        if self.vs_timer_interrupted() {
            self.handle_vs_interrupt();
        }

        if let Some(v) = self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp {
            let cycles_left = if v > self.current_time { v - self.current_time } else { 0 };
            self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp = Some(cycles_left);
        }

        self.set_s_timer();
    }

    pub fn restore_vs_timer(&mut self) {
        // let current_time = self.current_time();
        // let mtimer = self.read_m_timer(confidential_flow);
        // debug!("{:x}", mtimer - current_time);
        self.confidential_flow.confidential_hart_mut().csrs_mut().stimecmp = self.current_time + 80000;

        if let Some(v) = self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp {
            // debug!("left {:x}", v);
            self.confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp = self.current_time.checked_add(v);

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

    fn read_m_timer(&mut self) -> usize {
        self.confidential_flow.swap_mscratch();
        let m_timer = (unsafe { sbi_timer_value() }) as usize;
        self.confidential_flow.swap_mscratch();
        m_timer
    }

    fn set_m_timer(&mut self, next_event: usize) {
        self.confidential_flow.swap_mscratch();
        unsafe { sbi_timer_event_start(next_event as u64) };
        self.confidential_flow.swap_mscratch();
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
}
