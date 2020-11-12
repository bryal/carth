use crate::io::*;

use rustls::*;
use webpki;

use std::net::TcpStream;
use std::sync::Arc;

use crate::*;

#[repr(u8)]
pub enum Verifier {
    DangerousNone,
    Tofu,
}

impl ServerCertVerifier for Verifier {
    fn verify_server_cert(
        &self,
        _: &RootCertStore,
        _: &[Certificate],
        _: webpki::DNSNameRef<'_>,
        _: &[u8],
    ) -> Result<ServerCertVerified, TLSError> {
        match *self {
            Verifier::DangerousNone => Ok(ServerCertVerified::assertion()),
            Verifier::Tofu => todo!(),
        }
    }
}

#[no_mangle]
pub extern "C" fn stdrs_tcp_connect(host: Str, port: u16) -> FfiHandle {
    handle_to_ffi(Box::into_raw(
        Box::new(TcpStream::connect((host.as_str(), port)).expect("socket")) as _,
    ))
}

// Would have loved to use rustls for this, since it's rust, but there are problems that
// prevent it's effecient usage when using self signed certs as we do in gemini. See
// https://github.com/briansmith/webpki/issues/90.
#[no_mangle]
pub unsafe extern "C" fn stdrs_tls_connect(domain: Str, transport: FfiHandle) -> FfiHandle {
    let domain = domain.as_str();
    let transport = handle_from_ffi(transport);
    let mut config = rustls::ClientConfig::new();
    config
        .dangerous()
        .set_certificate_verifier(Arc::new(Verifier::DangerousNone));
    let dns_name = webpki::DNSNameRef::try_from_ascii_str(domain).expect("dns name");
    let sess = rustls::ClientSession::new(&Arc::new(config), dns_name);
    let tls = rustls::StreamOwned::new(sess, Box::from_raw(transport));
    handle_to_ffi(Box::into_raw(Box::new(tls) as _))
}

// fn main() {
//     // let (domain, path) = ("gus.guru", "/search");
//     let (domain, path) = ("gemini.circumlunar.space", "/");
//     let port = 1965;
//     get_data(domain, path, port);
//     // let header = resp.lines().next().expect("number of response lines >= 1");
//     // let code = header[0..2]
//     //     .parse::<u8>()
//     //     .expect("header beginning with 2-digit status code");
//     // let meta = &header[3..];
//     // if meta.as_bytes().len() > 1024 {
//     //     panic!("Response META longer than 1024 bytes. Error.");
//     // }
//     // let body = &resp[header.len() + 2..];
//     // println!("code: {}, meta: {}, body:\n\n{}", code, meta, body);
// }

// fn get_data(domain: &str, path: &str, port: u16) {
//     let mut config = ClientConfig::new();
//     config
//         .dangerous()
//         .set_certificate_verifier(Arc::new(Verifier::DangerousNone));
//     let dns_name = webpki::DNSNameRef::try_from_ascii_str(domain).expect("dns name");
//     let sess = ClientSession::new(&Arc::new(config), dns_name);
//     let sock = TcpStream::connect((domain, port)).expect("socket");
//     let mut tls = StreamOwned::new(sess, sock);
//     write!(&mut tls, "gemini://{}{}\r\n", domain, path).expect("written gemini message");
//     let code = &mut [0u8; 2][..];
//     tls.read_exact(code).unwrap();
//     let code = str::from_utf8(code).expect("valid utf-8 gemini status code");
//     println!("code: {}", code);
//     let mut resp = Vec::new();
//     println!("read result: {:?}\n", tls.read_to_end(&mut resp));
//     String::from_utf8(resp).expect("valid utf-8 response")
// }
