#![feature(const_fn)]

use std::ptr;

pub type Captures = *const ();
pub type ClosureFunc<A, B> = extern "C" fn(Captures, A) -> B;

#[repr(C)]
pub struct Closure<A, B> {
    captures: Captures,
    func: ClosureFunc<A, B>,
}

unsafe impl<A, B> Sync for Closure<A, B> {}

impl<A, B> Closure<A, B> {
    const fn new(f: ClosureFunc<A, B>) -> Closure<A, B> {
        Closure {
            captures: ptr::null(),
            func: f,
        }
    }
}

#[export_name = "print-int"]
pub static PRINT_INT: Closure<i64, ()> = Closure::new(print_int);

pub extern "C" fn print_int(_: Captures, n: i64) {
    println!("{}", n)
}
