//! Actual Shieldd KA API interval, with a public peer fixed by the snapshot.
//! The analyzer varies the canonical Montgomery Fr independently in each run.
use decaf377::{Element, Fr};
use decaf377_ka::{Public, Secret};
use std::ptr::{addr_of, addr_of_mut, read_volatile, write_volatile};

#[no_mangle]
pub static mut decaf_secret: Fr = Fr::ONE;
#[no_mangle]
pub static mut decaf_peer: [u8; 32] = [0; 32];
#[no_mangle]
pub static mut decaf_output: [u8; 32] = [0; 32];
// Deliberately unsafe trace fixture, enabled only for the analyzer's negative control.
#[cfg(decaf_address_control)]
#[no_mangle]
pub static mut decaf_control_slots: [u8; 2] = [0; 2];

#[cfg(decaf_address_control)]
#[no_mangle]
#[inline(never)]
pub extern "C" fn decaf_control_store() {
    unsafe {
        let index = (read_volatile(addr_of!(decaf_secret).cast::<u8>()) & 1) as usize;
        write_volatile(addr_of_mut!(decaf_control_slots).cast::<u8>().add(index), 1);
    }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn decaf_done() {
    unsafe { std::hint::black_box(read_volatile(addr_of!(decaf_output))); }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn decaf_entry() {
    let scalar = unsafe { read_volatile(addr_of!(decaf_secret)) };
    #[cfg(decaf_address_control)]
    decaf_control_store();
    let peer = Public(unsafe { read_volatile(addr_of!(decaf_peer)) });
    let secret = Secret::new_from_field(scalar);
    let shared = secret.key_agreement_with(&peer).expect("valid public peer");
    unsafe { write_volatile(addr_of_mut!(decaf_output), shared.0); }
    // Include destruction of the API's secret wrappers before the endpoint.
    drop(shared);
    drop(secret);
    decaf_done();
}

fn main() {
    assert_eq!(std::mem::size_of::<Fr>(), 32);
    unsafe {
        write_volatile(addr_of_mut!(decaf_peer), Element::GENERATOR.compress().0);
    }
    decaf_entry();
    let expected = Element::GENERATOR.compress().0;
    assert_eq!(unsafe { read_volatile(addr_of!(decaf_output)) }, expected);
}
