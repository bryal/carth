#![allow(non_camel_case_types)]

mod ffi;

use libc::*;
use std::io::{self, Write};
use std::{alloc, mem, slice, str};

#[no_mangle]
pub extern "C" fn install_stackoverflow_handler() {
    extern "C" fn stackoverflow_handler(_emergency: c_int, _scp: ffi::stackoverflow_context_t) {
        println!("Stack overflow");
    }

    let extra_stack_size = 16 << 10; // 16 KB ought to be enough for anybody
    let extra_stack = heap_alloc(extra_stack_size);
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

impl<A> Array<A>
where
    A: Clone,
{
    fn new(src: &[A]) -> Array<A> {
        unsafe {
            let len = src.len();
            let p = ffi::GC_malloc(len * mem::size_of::<A>()) as *mut A;
            let dest = slice::from_raw_parts_mut(p, len);
            dest.clone_from_slice(src);
            Array {
                elems: p,
                len: len as u64,
            }
        }
    }
}

#[repr(C)]
pub struct Str {
    array: Array<u8>,
}

impl Str {
    fn new(s: &str) -> Str {
        Str {
            array: Array::new(s.as_bytes()),
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

fn heap_alloc(size: u64) -> *mut u8 {
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
    Str::new(&(s1.to_string() + s2))
}

fn from_carth_str<'s>(s: &'s Str) -> &'s str {
    unsafe {
        let Array { elems, len } = s.array;
        let slice = slice::from_raw_parts(elems, len as usize);
        str::from_utf8_unchecked(slice)
    }
}

#[export_name = "show-int"]
pub extern "C" fn show_int(n: i64) -> Str {
    Str::new(&n.to_string())
}

#[export_name = "show-nat"]
pub extern "C" fn show_nat(n: u64) -> Str {
    Str::new(&n.to_string())
}

#[export_name = "show-f64"]
pub extern "C" fn show_f64(n: f64) -> Str {
    Str::new(&n.to_string())
}

#[export_name = "-panic"]
pub extern "C" fn panic(s: Str) {
    eprintln!("*** Panic: {}", from_carth_str(&s));
    std::process::abort()
}

// NOTE: This is a hack to ensure that Rust links in libm.
//
//       It seems that if no non-dead code makes use of functions from libm, then rustc or
//       cargo won't link with libm. However, we need that to happen, as when running a
//       Carth program with the JIT, there is no shared library for libm to load, so we
//       need the libm functionality to be included in libforeign_core.so.
//
// TODO: Find some other way of ensuring libm is linked with when creating the shared lib.
#[no_mangle]
pub extern "C" fn dummy_ensure_rust_links_libm(a: f64) -> f64 {
    f64::sin(a)
}
