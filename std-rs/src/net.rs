use crate::io::*;

use native_tls;

use std::net::{TcpStream, ToSocketAddrs};
use std::time::Duration;

use crate::*;

#[repr(C)]
pub struct Certificate {
    pub host: Str,
    pub fingerprint: Str,
}

#[no_mangle]
pub extern "C" fn stdrs_tcp_connect(host: Str, port: u16) -> Maybe<FfiHandle> {
    Maybe::Some(handle_to_ffi(Box::into_raw(Box::new(
        match TcpStream::connect((host.as_str(), port)).ok() {
            Some(x) => x,
            None => return Maybe::None,
        },
    ) as _)))
}

#[no_mangle]
pub extern "C" fn stdrs_tcp_connect_timeout(host: Str, port: u16, ms: u64) -> Maybe<FfiHandle> {
    let timeout = Duration::from_millis(ms);
    let addrs = match (host.as_str(), port).to_socket_addrs().ok() {
        Some(x) => x,
        None => return Maybe::None,
    }
    .collect::<Vec<_>>();
    let (last, init) = addrs.split_last().unwrap();
    if let Some(con) = init
        .iter()
        .find_map(|addr| TcpStream::connect_timeout(addr, timeout).ok())
        .or_else(|| TcpStream::connect_timeout(last, timeout).ok())
    {
        Maybe::Some(handle_to_ffi(Box::into_raw(Box::new(con) as _)))
    } else {
        Maybe::None
    }
}

/// Open a TLS connection over some transport channel (e.g. a TCP stream) without
/// performing any validation of the certificate. Dangerous!
#[no_mangle]
pub unsafe extern "C" fn stdrs_tls_connect_without_validation(
    domain: Str,
    transport: FfiHandle,
) -> Maybe<FfiHandle> {
    let domain = domain.as_str();
    let transport = Box::from_raw(handle_from_ffi(transport));
    let connector = match native_tls::TlsConnector::builder()
        .danger_accept_invalid_certs(true)
        // Rust's native-tls does not yet provide Tlsv13 :(
        .min_protocol_version(Some(native_tls::Protocol::Tlsv12))
        .build()
        .ok()
    {
        Some(x) => x,
        None => return Maybe::None,
    };
    let tls = match connector
        .connect(domain, transport)
        .map_err(show_tls_err)
        .ok()
    {
        Some(x) => x,
        None => return Maybe::None,
    };
    Maybe::Some(handle_to_ffi(Box::into_raw(Box::new(tls) as _)))
}

// Would have loved to use rustls for this, since it's rust, but there are problems that
// prevent it's efficent usage when using self signed certs as we do in gemini. See
// https://github.com/briansmith/webpki/issues/90.
//
/// Open a TLS connection over some transport channel (e.g. a TCP stream), validating the
/// certificate with TOFU. Useful for protocols like Gemini, which prefer decentralization
/// and self signing over relying on CAs.
#[no_mangle]
pub unsafe extern "C" fn stdrs_tls_connect_tofu(
    domain: Str,
    _known_hosts: Array<Certificate>,
    transport: FfiHandle,
) -> Maybe<FfiHandle> {
    let domain = domain.as_str();
    let transport = Box::from_raw(handle_from_ffi(transport));
    // We typically use self signed certs and TOFU in Gemini, but self signed certs are
    // considered "invalid" by default. Therefore, we accept invalid certs, but check for
    // expiration later.
    let connector = match native_tls::TlsConnector::builder()
        .danger_accept_invalid_certs(true)
        // Rust's native-tls does not yet provide Tlsv13 :(
        .min_protocol_version(Some(native_tls::Protocol::Tlsv12))
        .build()
        .ok()
    {
        Some(x) => x,
        None => return Maybe::None,
    };
    let _tls = match connector
        .connect(domain, transport)
        .map_err(show_tls_err)
        .ok()
    {
        Some(x) => x,
        None => return Maybe::None,
    };
    // TODO: See https://github.com/jansc/ncgopher/blob/26762fdcec959cc847d055372269b948cbee6822/src/controller.rs#L270-L336
    todo!("Check for cert expiration date and do TOFU")
}

fn show_tls_err<S>(e: native_tls::HandshakeError<S>) -> String {
    use native_tls::HandshakeError::*;
    match e {
        Failure(e) => e.to_string(),
        WouldBlock(_) => "the handshake process was interrupted".to_string(),
    }
}
