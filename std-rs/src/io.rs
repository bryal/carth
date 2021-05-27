use std::io::{self, Read, Write};
use std::mem;

use crate::*;

pub trait ReadWrite: Read + Write {}

impl<T> ReadWrite for T where T: Read + Write {}

pub type Handle = *mut dyn ReadWrite;

#[derive(Clone, Copy)]
#[repr(C)]
pub struct FfiHandle(*mut u8, *mut u8);

pub fn handle_to_ffi(h: Handle) -> FfiHandle {
    unsafe { mem::transmute(h) }
}

pub unsafe fn handle_from_ffi(h: FfiHandle) -> Handle {
    mem::transmute(h)
}

#[no_mangle]
pub unsafe extern "C" fn stdrs_close_handle(h: FfiHandle) {
    drop(Box::from_raw(handle_from_ffi(h)))
}

#[no_mangle]
pub unsafe extern "C" fn stdrs_read_handle(
    h: FfiHandle,
    mut buf: Array<u8>,
) -> Maybe<Cons<Array<u8>, usize>> {
    let res = (*handle_from_ffi(h)).read(buf.as_slice_mut());
    match res {
        Ok(n) => Maybe::Some(Cons(buf, n)),
        Err(ref e) if e.kind() == io::ErrorKind::Interrupted => stdrs_read_handle(h, buf),
        Err(_) => Maybe::None,
    }
}

#[no_mangle]
pub unsafe extern "C" fn stdrs_write_handle(h: FfiHandle, buf: Array<u8>) -> Maybe<usize> {
    let res = (*handle_from_ffi(h)).write(buf.as_slice());
    match res {
        Ok(n) => Maybe::Some(n),
        Err(ref e) if e.kind() == io::ErrorKind::Interrupted => Maybe::Some(0),
        Err(_) => Maybe::None,
    }
}
