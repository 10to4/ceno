#![deny(clippy::cargo)]
#![feature(strict_overflow_ops)]
#![no_std]

use core::arch::{asm, global_asm};

mod allocator;

mod mmio;
pub use mmio::{read, read_slice};

mod io;
pub use io::info_out;

mod params;
pub use params::*;

#[cfg(not(test))]
mod panic_handler {
    use core::panic::PanicInfo;

    #[panic_handler]
    #[inline(never)]
    fn panic_handler(_panic: &PanicInfo<'_>) -> ! {
        super::halt(1)
    }
}

#[allow(asm_sub_register)]
pub fn halt(exit_code: u32) -> ! {
    unsafe {
        asm!(
            "ecall",
            in ("a0") exit_code,
            in ("t0") 0,
        );
    }
    unreachable!();
}

global_asm!(
    "
// The entry point for the program.
.section .init
.global _start
_start:

    // Set the global pointer somewhere towards the start of RAM.
    .option push
    .option norelax
    la gp, __global_pointer$
    .option pop

    // Set the stack pointer and frame pointer to the top of the stack.
    la sp, _stack_start
    mv fp, sp

    // Call the Rust start function.
    jal zero, _start_rust
    ",
);

#[macro_export]
macro_rules! entry {
    ($path:path) => {
        // Type check the given path
        const CENO_ENTRY: fn() = $path;

        mod ceno_generated_main {
            #[no_mangle]
            extern "C" fn bespoke_entrypoint() {
                super::CENO_ENTRY();
            }
        }
    };
}

/// _start_rust is called by the assembly entry point and it calls the Rust main().
#[no_mangle]
unsafe extern "C" fn _start_rust() -> ! {
    extern "C" {
        fn bespoke_entrypoint();
    }
    bespoke_entrypoint();
    halt(0)
}

extern "C" {
    // The address of this variable is the start of the stack (growing downwards).
    static _stack_start: u8;
}
