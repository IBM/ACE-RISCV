extern "C" {
    fn _acquire(address: usize);
    fn _release(address: usize);
}

pub static UART_SYNC_ADDRESS: usize = 0x8009D000;

pub fn acquire(address: usize) {
    unsafe { _acquire(address) };
}

pub fn release(address: usize) {
    unsafe { _release(address) };
}
