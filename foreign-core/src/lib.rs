#![feature(const_fn)]

use std::io::{self, Write};
use std::{alloc, ptr, slice, str};

macro_rules! def_carth_closure {
    ($e:expr, $s:ident, $f:ident; $ta:ty, $tr:ty; $a:pat => $b:expr) => {
        #[export_name = $e]
        pub static $s: Closure<$ta, $tr> = Closure::new($f);
        pub extern "C" fn $f(_: Captures, $a: $ta) -> $tr {
            $b
        }
    };
}

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

def_carth_closure! {
    "display-inline", DISPLAY_INLINE, display_inline;
    Str, (); s => {
        let s = from_carth_str(&s);
        print!("{}", s);
        io::stdout().flush().ok();
    }
}

def_carth_closure! {
    "-str-append", STR_APPEND, str_append;
    Pair<Str, Str>, Str; Pair { fst, snd, .. } => {
        let (s1, s2) = (from_carth_str(&fst), from_carth_str(&snd));
        Str::new(s1.to_string() + s2)
    }
}

fn from_carth_str<'s>(s: &'s Str) -> &'s str {
    unsafe {
        let Array { elems, len, .. } = s.array;
        let slice = slice::from_raw_parts(elems, len as usize);
        str::from_utf8_unchecked(slice)
    }
}

def_carth_closure! {
    "add-int", ADD_INT, add_int;
    Pair<i64, i64>, i64; Pair { fst, snd, .. } => fst + snd
}

def_carth_closure! {
    "gt-int", GT_INT, gt_int;
    Pair<i64, i64>, bool; Pair { fst, snd, .. } => fst > snd
}

def_carth_closure! {
    "eq-int", EQ_INT, eq_int;
    Pair<i64, i64>, bool; Pair { fst, snd, .. } => fst == snd
}

def_carth_closure! {
    "show-int", SHOW_INT, show_int;
    i64, Str; n =>
        Str::new(n.to_string())
}
