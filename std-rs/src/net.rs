use crate::io::*;

use native_tls;

use std::net::{TcpStream, ToSocketAddrs};
use std::time::Duration;

use crate::*;

#[no_mangle]
pub extern "C" fn stdrs_tcp_connect(host: Str, port: u16) -> FfiHandle {
    handle_to_ffi(Box::into_raw(
        Box::new(TcpStream::connect((host.as_str(), port)).expect("socket")) as _,
    ))
}

#[no_mangle]
pub extern "C" fn stdrs_tcp_connect_timeout(host: Str, port: u16, ms: u64) -> FfiHandle {
    let timeout = Duration::from_millis(ms);
    let addrs = (host.as_str(), port)
        .to_socket_addrs()
        .unwrap()
        .collect::<Vec<_>>();
    let (last, init) = addrs.split_last().unwrap();
    let con = init
        .iter()
        .filter_map(|addr| TcpStream::connect_timeout(addr, timeout).ok())
        .next()
        .unwrap_or_else(|| TcpStream::connect_timeout(last, timeout).unwrap());
    handle_to_ffi(Box::into_raw(Box::new(con) as _))
}

// Would have loved to use rustls for this, since it's rust, but there are problems that
// prevent it's effecient usage when using self signed certs as we do in gemini. See
// https://github.com/briansmith/webpki/issues/90.
#[no_mangle]
pub unsafe extern "C" fn stdrs_tls_connect(domain: Str, transport: FfiHandle) -> FfiHandle {
    let domain = domain.as_str();
    let transport = Box::from_raw(handle_from_ffi(transport));
    // We typically use self signed certs and TOFU in Gemini, but self signed certs are
    // considered "invalid" by default. Therefore, we accept invalid certs, but check for
    // expiration later.
    let connector = native_tls::TlsConnector::builder()
        // TODO: Check for cert expiration date and do TOFU.
        .danger_accept_invalid_certs(true)
        // Rust's native-tls does not yet provide Tlsv13 :(
        .min_protocol_version(Some(native_tls::Protocol::Tlsv12))
        .build()
        .unwrap();
    let tls = connector
        .connect(domain, transport)
        .map_err(show_tls_err)
        .unwrap();
    handle_to_ffi(Box::into_raw(Box::new(tls) as _))
}

fn show_tls_err<S>(e: native_tls::HandshakeError<S>) -> String {
    use native_tls::HandshakeError::*;
    match e {
        Failure(e) => e.to_string(),
        WouldBlock(_) => "the handshake process was interrupted".to_string(),
    }
}
