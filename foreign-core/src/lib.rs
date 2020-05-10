#![allow(non_camel_case_types)]

mod ffi;

use libc::*;
use std::io::{self, Write};
use std::{alloc, slice, str};

#[no_mangle]
pub extern "C" fn install_stackoverflow_handler() {
    extern "C" fn stackoverflow_handler(_emergency: c_int, _scp: ffi::stackoverflow_context_t) {
        println!("Stack overflow");
    }

    let extra_stack_size = 16 << 10; // 16 KB ought to be enough for anybody
    let extra_stack = carth_alloc(extra_stack_size);
    unsafe {
        ffi::stackoverflow_install_handler(
            stackoverflow_handler,
            extra_stack as *mut _,
            extra_stack_size as usize,
        );
    }
}

#[repr(C)]
pub struct Array<A> {
    elems: *mut A,
    len: u64,
}

impl<A> Array<A> {
    fn new(xs: Vec<A>) -> Array<A> {
        let len = xs.len() as u64;
        Array {
            elems: Box::into_raw(xs.into_boxed_slice()) as *mut A,
            len,
        }
    }
}

#[repr(C)]
pub struct Str {
    array: Array<u8>,
}

impl Str {
    fn new(s: String) -> Str {
        Str {
            array: Array::new(s.into_bytes()),
        }
    }
}

#[repr(C)]
pub struct Pair<A, B> {
    fst: A,
    snd: B,
}

// TODO: Do it properly.
//       https://en.cppreference.com/w/c/types/max_align_t
const MAX_ALIGN: usize = 8;

#[no_mangle]
pub extern "C" fn carth_alloc(size: u64) -> *mut u8 {
    unsafe { alloc::alloc(alloc::Layout::from_size_align(size as usize, MAX_ALIGN).unwrap()) }
}

#[no_mangle]
pub extern "C" fn carth_str_eq(s1: Str, s2: Str) -> bool {
    let (s1, s2) = (from_carth_str(&s1), from_carth_str(&s2));
    s1 == s2
}

#[export_name = "display-inline"]
pub extern "C" fn display_inline(s: Str) {
    let s = from_carth_str(&s);
    print!("{}", s);
    io::stdout().flush().ok();
}

#[export_name = "str-append"]
pub extern "C" fn str_append(s1: Str, s2: Str) -> Str {
    let (s1, s2) = (from_carth_str(&s1), from_carth_str(&s2));
    Str::new(s1.to_string() + s2)
}

fn from_carth_str<'s>(s: &'s Str) -> &'s str {
    unsafe {
        let Array { elems, len } = s.array;
        let slice = slice::from_raw_parts(elems, len as usize);
        str::from_utf8_unchecked(slice)
    }
}

#[export_name = "+i"]
pub extern "C" fn add_int(a: i64, b: i64) -> i64 {
    a + b
}

#[export_name = "-i"]
pub extern "C" fn sub_int(a: i64, b: i64) -> i64 {
    a - b
}

#[export_name = "*i"]
pub extern "C" fn mul_int(a: i64, b: i64) -> i64 {
    a * b
}

#[export_name = "/i"]
pub extern "C" fn div_int(a: i64, b: i64) -> i64 {
    a / b
}

#[export_name = "remi"]
pub extern "C" fn rem_int(a: i64, b: i64) -> i64 {
    a % b
}

#[export_name = ">i"]
pub extern "C" fn gt_int(a: i64, b: i64) -> bool {
    a > b
}

#[export_name = "=i"]
pub extern "C" fn eq_int(a: i64, b: i64) -> bool {
    a == b
}

#[export_name = "show-int"]
pub extern "C" fn show_int(n: i64) -> Str {
    Str::new(n.to_string())
}

#[export_name = "+f"]
pub extern "C" fn add_f64(a: f64, b: f64) -> f64 {
    a + b
}

#[export_name = "-f"]
pub extern "C" fn sub_f64(a: f64, b: f64) -> f64 {
    a - b
}

#[export_name = "*f"]
pub extern "C" fn mul_f64(a: f64, b: f64) -> f64 {
    a * b
}

#[export_name = "/f"]
pub extern "C" fn div_f64(a: f64, b: f64) -> f64 {
    a / b
}

#[export_name = "remf"]
pub extern "C" fn rem_f64(a: f64, b: f64) -> f64 {
    a % b
}

#[export_name = ">f"]
pub extern "C" fn gt_f64(a: f64, b: f64) -> bool {
    a > b
}

#[export_name = "=f"]
pub extern "C" fn eq_f64(a: f64, b: f64) -> bool {
    a == b
}

#[export_name = "show-f64"]
pub extern "C" fn show_f64(n: f64) -> Str {
    Str::new(n.to_string())
}

#[export_name = "-panic"]
pub extern "C" fn panic(s: Str) {
    eprintln!("*** Panic: {}", from_carth_str(&s));
    std::process::abort()
}
