//! Binary-analysis boundary: canonical Montgomery Fr, public generator.
use decaf377::{Element, Fr};
use std::ptr::{addr_of, addr_of_mut, read_volatile, write_volatile};

#[no_mangle]
pub static mut decaf_secret: Fr = Fr::ONE;
#[no_mangle]
pub static mut decaf_output: Element = Element::IDENTITY;

#[no_mangle]
#[inline(never)]
pub extern "C" fn decaf_done() {
    unsafe { std::hint::black_box(read_volatile(addr_of!(decaf_output))); }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn decaf_entry() {
    let scalar = unsafe { read_volatile(addr_of!(decaf_secret)) };
    let result = Element::GENERATOR * scalar;
    unsafe { write_volatile(addr_of_mut!(decaf_output), result); }
    decaf_done();
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn decaf_mut_entry() {
    let mut scalar = unsafe { read_volatile(addr_of!(decaf_secret)) };
    let mut result = Element::GENERATOR;
    result *= &mut scalar;
    unsafe { write_volatile(addr_of_mut!(decaf_output), result); }
    decaf_done();
}

fn main() {
    assert_eq!(std::mem::size_of::<Fr>(), 32);
    decaf_entry();
    decaf_mut_entry();
}
