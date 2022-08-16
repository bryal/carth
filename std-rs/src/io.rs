use std::io::{self, Read, Write};
use std::mem;

use crate::*;

pub trait ReadWrite: Read + Write {}

impl<T> ReadWrite for T where T: Read + Write {}

pub type Handle = *mut dyn ReadWrite;

#[derive(Clone, Copy)]
#[repr(C)]
pub struct FfiHandle(*mut u8, *mut u8);

pub unsafe fn handle_to_ffi(h: Handle) -> FfiHandle {
    mem::transmute(h)
}

pub unsafe fn handle_from_ffi(h: FfiHandle) -> Handle {
    mem::transmute(h)
}

#[no_mangle]
pub unsafe extern "C" fn stdrs_close_handle(h: FfiHandle) {
    drop(Box::from_raw(handle_from_ffi(h)))
}

struct MyStdin(std::io::Stdin);

impl std::io::Read for MyStdin {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.0.read(buf)
    }
}

impl std::io::Write for MyStdin {
    fn write(&mut self, _buf: &[u8]) -> std::io::Result<usize> {
        Err(std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            "cannot write to stdin",
        ))
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Err(std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            "cannot flush stdin as output stream",
        ))
    }
}

#[no_mangle]
pub unsafe extern "C" fn stdrs_stdin_handle() -> FfiHandle {
    handle_to_ffi(Box::into_raw(Box::new(MyStdin(std::io::stdin())) as _))
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

#[no_mangle]
pub unsafe extern "C" fn call_process(
    cmd: Str,
    args: Array<Str>,
) -> Maybe<Cons<Array<u8>, Cons<Array<u8>, Cons<Maybe<i32>, ()>>>> {
    if let Ok(output) = std::process::Command::new(cmd.as_str())
        .args(args.as_slice().iter().map(|s| s.as_str()))
        .output()
    {
        Maybe::Some(Cons(
            Array::new(&output.stdout),
            Cons(
                Array::new(&output.stderr),
                Cons(output.status.code().into(), ()),
            ),
        ))
    } else {
        Maybe::None
    }
}

#[no_mangle]
pub extern "C" fn get_contents() -> Str {
    let mut s = String::new();
    std::io::stdin()
        .read_to_string(&mut s)
        .expect("read all of stdin");
    Str::new(&s)
}

#[no_mangle]
pub extern "C" fn read_file(fp: Str) -> Maybe<Str> {
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

#[no_mangle]
pub extern "C" fn write_file(fp: Str, s: Str) -> Maybe<()> {
    let fp = fp.as_str();
    File::create(fp)
        .ok()
        .map(|mut f| {
            f.write_all(s.as_str().as_bytes())
                .ok()
                .map(|()| Maybe::Some(()))
                .unwrap_or(Maybe::None)
        })
        .unwrap_or(Maybe::None)
}

#[no_mangle]
pub extern "C" fn get_args() -> Array<Str> {
    Array::new(&std::env::args().map(|s| Str::new(&s)).collect::<Vec<Str>>())
}
