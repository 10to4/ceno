#![no_main]
#![no_std]

extern crate ceno_rt;
use ceno_rt::println;
use core::fmt::Write;
use core::ops::Range;

// Use volatile functions to prevent compiler optimizations.
use core::ptr::{read_volatile, write_volatile};

const HINTS: Range<usize> = 0x4000_0000..0x5000_0000;

// const OUTPUT_ADDRESS: u32 = 0x8000_0000;

ceno_rt::entry!(main);
fn main() {
    let x: u32 = unsafe { read_volatile(HINTS.start as *mut u32)};
    assert_eq!(x, 0xdead_beef);
    // assert_eq!(x, 0);
}
