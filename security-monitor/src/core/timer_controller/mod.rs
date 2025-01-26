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

const NOT_INITIALIZED_TIMER_CONTROLLER: &str = "Bug. Could not access timer controller because it has not been initialized";

pub static TIMER_CONTROLLER: Once<RwLock<TimerController>> = Once::new();

pub struct TimerController {}

impl<'a> TimerController {
    pub fn initialize() -> Result<(), Error> {
        let controller = Self::new()?;
        ensure_not!(TIMER_CONTROLLER.is_completed(), Error::Reinitialization())?;
        TIMER_CONTROLLER.call_once(|| RwLock::new(controller));
        Ok(())
    }

    fn new() -> Result<Self, Error> {
        Ok(Self {})
    }

    pub fn set_next_event_for_vs_mode(&mut self, confidential_flow: &mut ConfidentialFlow, ncycle: usize) {
        confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp = ncycle;
        if self.is_vs_timer_running(confidential_flow) {
            self.set_vs_timer(confidential_flow, ncycle);
        }
    }

    fn is_vs_timer_programmed(&mut self, confidential_flow: &mut ConfidentialFlow) -> bool {
        let vstimecmp = confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp;
        vstimecmp > 0 && vstimecmp < usize::MAX - 1
    }

    fn is_vs_timer_running(&mut self, confidential_flow: &mut ConfidentialFlow) -> bool {
        let stimecmp = confidential_flow.confidential_hart_mut().csrs_mut().stimecmp;
        let vstimecmp = confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp;
        vstimecmp > 0 && vstimecmp <= stimecmp
    }

    pub fn s_timer_interrupted(&mut self, confidential_flow: &mut ConfidentialFlow, mtime: usize) -> bool {
        let stimecmp = confidential_flow.confidential_hart_mut().csrs_mut().stimecmp;
        mtime >= stimecmp
    }

    pub fn vs_timer_interrupted(&mut self, confidential_flow: &mut ConfidentialFlow, mtime: usize) -> bool {
        let vstimecmp = confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp;
        vstimecmp > 0 && mtime >= vstimecmp
    }

    pub fn handle_vs_interrupt(&mut self, confidential_flow: &mut ConfidentialFlow) {
        // debug!("Inject VSTIP");
        confidential_flow.confidential_hart_mut().csrs_mut().vstip |= MIE_VSTIP_MASK;
        // confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp = usize::MAX - 1;
    }

    pub fn store_vs_timer(&mut self, confidential_flow: &mut ConfidentialFlow) {
        let vstimecmp = confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp;
        let stimecmp = confidential_flow.confidential_hart_mut().csrs_mut().stimecmp;
        let mtime = self.read_mtime();

        // debug!("store_vs_timer mtime={:x} vstimecmp={:x} stimecmp={:x}", mtime, vstimecmp, stimecmp);
        if self.vs_timer_interrupted(confidential_flow, mtime) {
            self.handle_vs_interrupt(confidential_flow);
        }
        self.set_s_timer(confidential_flow, stimecmp);

        let cycles_left = if vstimecmp > mtime && vstimecmp < usize::MAX - 1 { vstimecmp - mtime } else { usize::MAX - 1 };
        if cycles_left > 0 && cycles_left < usize::MAX - 1 {
            // debug!("Cycles lesft {:x}", cycles_left);
        }
        confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp = cycles_left;
    }

    pub fn restore_vs_timer(&mut self, confidential_flow: &mut ConfidentialFlow) {
        let mtime = self.read_mtime();
        let old_timer = self.read_m_timer(confidential_flow);
        confidential_flow.confidential_hart_mut().csrs_mut().stimecmp = old_timer + 50000;
        let vstimecmp = confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp;

        // timer not programmed then nothing to restore
        if !self.is_vs_timer_programmed(confidential_flow) {
            return;
        }

        let new_timer = mtime + vstimecmp;
        // debug!("restore_vs_timer mtime={:x} vstimecmp={:x} stimecmp={:x} new_timer={:x}", mtime, vstimecmp, old_timer, new_timer);
        confidential_flow.confidential_hart_mut().csrs_mut().vstimecmp = new_timer;

        if self.vs_timer_interrupted(confidential_flow, mtime) {
            self.handle_vs_interrupt(confidential_flow);
        } else if self.is_vs_timer_running(confidential_flow) {
            self.set_vs_timer(confidential_flow, new_timer);
        }
    }

    pub fn set_vs_timer(&self, confidential_flow: &mut ConfidentialFlow, ncycle: usize) {
        // debug!("Restore VS timer {:x}", ncycle);
        self.set_m_timer(confidential_flow, ncycle);
        confidential_flow.confidential_hart_mut().csrs_mut().vstip &= !MIE_VSTIP_MASK;
        confidential_flow.confidential_hart_mut().csrs_mut().mip.read_and_clear_bits(MIE_MTIP_MASK);
    }

    pub fn set_s_timer(&self, confidential_flow: &mut ConfidentialFlow, ncycle: usize) {
        // debug!("Restore S timer {:x}", ncycle);
        self.set_m_timer(confidential_flow, ncycle);
        confidential_flow.confidential_hart_mut().csrs_mut().mip.read_and_clear_bits(MIE_MTIP_MASK);
    }

    pub fn read_mtime(&self) -> usize {
        CSR.time.read()
    }

    fn read_m_timer(&self, confidential_flow: &mut ConfidentialFlow) -> usize {
        confidential_flow.swap_mscratch();
        let m_timer = (unsafe { sbi_timer_value() }) as usize;
        confidential_flow.swap_mscratch();
        m_timer
    }

    fn set_m_timer(&self, confidential_flow: &mut ConfidentialFlow, ncycle: usize) {
        confidential_flow.swap_mscratch();
        unsafe { sbi_timer_event_start(ncycle as u64) };
        confidential_flow.swap_mscratch();
    }

    pub fn try_write<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&mut RwLockWriteGuard<'static, TimerController>) -> Result<F, Error> {
        op(&mut TIMER_CONTROLLER.get().expect(NOT_INITIALIZED_TIMER_CONTROLLER).write())
    }
}
