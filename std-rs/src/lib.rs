// #![feature(try_trait_v2)]
// #![feature(control_flow_enum)]
#![allow(non_camel_case_types)]

mod ffi;
pub mod io;
pub mod net;

use libc::*;
use std::fs::File;
use std::io::{Read, Write};
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
pub struct Cons<A, B>(pub A, pub B);

#[repr(C)]
pub struct Array<A> {
    elems: *mut A,
    len: u64,
}

impl<A> Array<A>
where
    A: Clone,
{
    pub fn new(src: &[A]) -> Array<A> {
        unsafe {
            let len = src.len();
            let p = ffi::GC_malloc(len * mem::size_of::<A>()) as *mut A;
            // let p = std::alloc::alloc(
            //     std::alloc::Layout::from_size_align(
            //         len * mem::size_of::<A>(),
            //         mem::align_of::<A>(),
            //     )
            //     .unwrap(),
            // ) as *mut A;
            let dest = slice::from_raw_parts_mut(p, len);
            dest.clone_from_slice(src);
            Array {
                elems: p,
                len: len as u64,
            }
        }
    }

    pub fn as_slice(&self) -> &[A] {
        unsafe { slice::from_raw_parts(self.elems, self.len as usize) }
    }

    pub fn as_slice_mut(&mut self) -> &mut [A] {
        unsafe { slice::from_raw_parts_mut(self.elems, self.len as usize) }
    }

    pub unsafe fn shallow_copy(&self) -> Self {
        Self {
            elems: self.elems,
            len: self.len,
        }
    }
}

#[repr(C)]
pub struct Str {
    pub array: Array<u8>,
}

impl Str {
    pub fn new(s: &str) -> Str {
        Str {
            array: Array::new(s.as_bytes()),
        }
    }

    pub fn as_str<'s>(&'s self) -> &'s str {
        unsafe {
            let Array { elems, len } = self.array;
            let slice = slice::from_raw_parts(elems, len as usize);
            str::from_utf8_unchecked(slice)
        }
    }

    pub unsafe fn shallow_copy(&self) -> Self {
        Self {
            array: self.array.shallow_copy(),
        }
    }
}

#[repr(C, u8)]
pub enum Maybe<A> {
    None,
    Some(A),
}

impl<A> Maybe<A> {
    pub fn unwrap(self) -> A {
        match self {
            Maybe::None => panic!("Maybe::unwrap on None"),
            Maybe::Some(a) => a,
        }
    }
}

#[repr(u8)]
pub enum Cmp {
    Lt,
    Eq,
    Gt,
}

// TODO: Do it properly.
//       https://en.cppreference.com/w/c/types/max_align_t
const MAX_ALIGN: usize = 8;

fn heap_alloc(size: u64) -> *mut u8 {
    unsafe { alloc::alloc(alloc::Layout::from_size_align(size as usize, MAX_ALIGN).unwrap()) }
}

#[no_mangle]
pub extern "C" fn str_eq(s1: Str, s2: Str) -> bool {
    let (s1, s2) = (s1.as_str(), s2.as_str());
    s1 == s2
}
#[no_mangle]
pub extern "C" fn str_cmp(s1: Str, s2: Str) -> Cmp {
    use std::cmp::Ordering::*;
    let (s1, s2) = (s1.as_str(), s2.as_str());
    match s1.cmp(s2) {
        Less => Cmp::Lt,
        Equal => Cmp::Eq,
        Greater => Cmp::Gt,
    }
}

#[no_mangle]
pub extern "C" fn str_show(s: Str) -> Str {
    let s = s.as_str();
    Str::new(&format!("{:?}", s))
}

#[no_mangle]
pub extern "C" fn unsafe_display_inline(s: Str) {
    let s = s.as_str();
    print!("{}", s);
    std::io::stdout().flush().ok();
}

#[no_mangle]
pub extern "C" fn str_append(s1: Str, s2: Str) -> Str {
    let (s1, s2) = (s1.as_str(), s2.as_str());
    Str::new(&(s1.to_string() + s2))
}

#[no_mangle]
pub extern "C" fn show_int(n: i64) -> Str {
    Str::new(&n.to_string())
}

#[no_mangle]
pub extern "C" fn show_nat(n: u64) -> Str {
    Str::new(&n.to_string())
}

#[no_mangle]
pub extern "C" fn show_f64(n: f64) -> Str {
    Str::new(&n.to_string())
}

#[no_mangle]
pub extern "C" fn _print_int(n: i64) {
    println!("_print_int: {}", n);
}

#[no_mangle]
pub extern "C" fn _panic(s: Str) {
    eprintln!("*** Panic: {}", s.as_str());
    std::process::abort()
}

#[no_mangle]
pub extern "C" fn _get_contents() -> Str {
    let mut s = String::new();
    std::io::stdin()
        .read_to_string(&mut s)
        .expect("read all of stdin");
    Str::new(&s)
}

#[no_mangle]
pub extern "C" fn unsafe_read_file(fp: Str) -> Maybe<Str> {
    let fp = fp.as_str();
    File::open(fp)
        .ok()
        .map(|mut f| {
            let mut s = String::new();
            f.read_to_string(&mut s)
                .ok()
                .map(|_| Maybe::Some(Str::new(&s)))
                .unwrap_or(Maybe::None)
        })
        .unwrap_or(Maybe::None)
}

// NOTE: This is a hack to ensure that Rust links in libm.
//
//       It seems that if no non-dead code makes use of functions from libm, then rustc or cargo
//       won't link with libm. However, we need that to happen, as when running a Carth program with
//       the JIT, there is no shared library for libm to load, so we need the libm functionality to
//       be included in the .so.
//
// TODO: Find some other way of ensuring libm is linked with when creating the shared lib.
#[no_mangle]
pub extern "C" fn dummy_ensure_rust_links_libm(a: f64) -> f64 {
    f64::sin(a)
}
