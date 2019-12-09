#![feature(const_fn)]

use std::io::{self, Write};
use std::{alloc, ptr, slice, str};

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

#[repr(C)]
pub struct Array<A> {
    _tag: u64,
    elems: *mut A,
    len: u64,
}

impl<A> Array<A> {
    fn new(xs: Vec<A>) -> Array<A> {
        let len = xs.len() as u64;
        Array {
            _tag: 0,
            elems: Box::into_raw(xs.into_boxed_slice()) as *mut A,
            len,
        }
    }
}

#[repr(C)]
pub struct Str {
    _tag: u64,
    array: Array<u8>,
}

impl Str {
    fn new(s: String) -> Str {
        Str {
            _tag: 0,
            array: Array::new(s.into_bytes()),
        }
    }
}

#[repr(C)]
pub struct Pair<A, B> {
    _tag: u64,
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

#[export_name = "display-inline"]
pub static DISPLAY_INLINE: Closure<*const Str, ()> = Closure::new(display_inline_f);
pub extern "C" fn display_inline_f(_: Captures, s: *const Str) {
    let s = unsafe { from_carth_str(&*s) };
    print!("{}", s);
    io::stdout().flush().ok();
}

#[export_name = "str-append"]
pub static STR_APPEND: Closure<*const Pair<Str, Str>, Str> = Closure::new(str_append_f);
pub extern "C" fn str_append_f(_: Captures, pair: *const Pair<Str, Str>) -> Str {
    let (s1, s2) = unsafe { (from_carth_str(&(*pair).fst), from_carth_str(&(*pair).snd)) };
    Str::new(s1.to_string() + s2)
}

fn from_carth_str(s: &Str) -> &str {
    unsafe {
        let Array { elems, len, .. } = (*s).array;
        let slice = slice::from_raw_parts(elems, len as usize);
        str::from_utf8_unchecked(slice)
    }
}
