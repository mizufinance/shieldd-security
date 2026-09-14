#![no_std]
#![no_main]

// The runner copies the pinned, unmodified native Fiat module beside this file.
mod fiat;

#[no_mangle]
static mut decaf_secret: [u32; 16] = [0; 16];
#[no_mangle]
static mut decaf_output: [u32; 8] = [0; 8];

#[no_mangle]
#[inline(never)]
pub fn decaf_done() {
    unsafe { core::ptr::read_volatile(core::ptr::addr_of!(decaf_output)); }
}

#[no_mangle]
#[inline(never)]
pub fn decaf_entry() {
    unsafe {
        let input = core::ptr::read_volatile(core::ptr::addr_of!(decaf_secret));
        let mut a = [0u32; 8];
        let mut b = [0u32; 8];
        a.copy_from_slice(&input[..8]);
        b.copy_from_slice(&input[8..]);
        let mut out = [0u32; 8];
        fiat::fq_add(&mut out, &a, &b);
        core::ptr::write_volatile(core::ptr::addr_of_mut!(decaf_output), out);
    }
    decaf_done();
}

#[no_mangle]
pub fn _start() -> ! {
    decaf_entry();
    loop {}
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
