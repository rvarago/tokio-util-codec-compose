//! A simple SOCKSv4 decoder without any validation during decoding.

use tokio_util_codec_compose::{combinators::DecoderExt, elements::*};

use anyhow::Result;
use bytes::BytesMut;
use std::net::Ipv4Addr;
use tokio_util::codec::Decoder;

fn main() -> Result<()> {
    let mut decoder = uint8()
        .then(uint8())
        .then(uint16_be())
        .then(ipv4())
        .then(delimited_by([b'\x00'], 255))
        .map(
            |((((version, command), destination_port), destination_ip), user_id)| SocksRequest {
                version,
                command,
                destination_port,
                destination_ip,
                user_id: String::from_utf8_lossy(&user_id).into_owned(),
            },
        );

    // SOCKS4 request to CONNECT "Fred" to 66.102.7.99:80 => "\x04\x01\x00\x50\x42\x66\x07\x63\x46\x72\x65\x64\x00"
    let mut src = BytesMut::from("\x04\x01");
    let res = decoder.decode(&mut src)?;

    assert_eq!(res, None);
    assert_eq!(src, BytesMut::from(""));

    let mut src = BytesMut::from("\x00\x50\x42\x66\x07\x63\x46\x72\x65\x64\x00");
    let res = decoder.decode(&mut src)?;

    assert_eq!(
        Some(SocksRequest {
            version: 0x04,
            command: 0x01,
            destination_port: 80,
            destination_ip: "66.102.7.99".parse()?,
            user_id: "Fred".into(),
        }),
        res
    );
    assert_eq!(src, BytesMut::from(""));

    dbg!(res);

    Ok(())
}

#[derive(Debug, PartialEq, Eq)]
struct SocksRequest {
    version: u8,
    command: u8,
    destination_port: u16,
    destination_ip: Ipv4Addr,
    user_id: String,
}
