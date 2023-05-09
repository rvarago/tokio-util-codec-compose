//! A SOCKSv4 decoder with validation interleaved with decoding.

use tokio_util_codec_compose::{combinators::DecoderExt, elements::*};

use anyhow::Result;
use bytes::BytesMut;
use std::{io, net::Ipv4Addr};
use tokio_util::codec::Decoder;

fn main() -> Result<()> {
    let mut decoder = uint8()
        .try_map(Version::try_from)
        .then(uint8().try_map(Command::try_from))
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

    // SOCKS4 invalid request (wrong version 0x05)

    let mut src = BytesMut::from("\x05");
    let res = decoder.decode(&mut src);

    assert!(res.is_err());

    // SOCKS4 valid request to CONNECT "Fred" to 66.102.7.99:80 => "\x04\x01\x00\x50\x42\x66\x07\x63\x46\x72\x65\x64\x00"

    let mut src = BytesMut::from("\x04\x01");
    let res = decoder.decode(&mut src)?;

    assert_eq!(res, None);
    assert_eq!(src, BytesMut::from(""));

    let mut src = BytesMut::from("\x00\x50\x42\x66\x07\x63\x46\x72\x65\x64\x00");
    let res = decoder.decode(&mut src)?;

    assert_eq!(
        Some(SocksRequest {
            version: Version::V4,
            command: Command::Connect,
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
    version: Version,
    command: Command,
    destination_port: u16,
    destination_ip: Ipv4Addr,
    user_id: String,
}

#[derive(Debug, PartialEq, Eq)]
enum Version {
    V4,
}

impl TryFrom<u8> for Version {
    type Error = io::Error;

    fn try_from(value: u8) -> std::result::Result<Self, Self::Error> {
        match value {
            0x04 => Ok(Version::V4),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "unexpected version {value}",
            )),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Command {
    Connect,
}

impl TryFrom<u8> for Command {
    type Error = io::Error;

    fn try_from(value: u8) -> std::result::Result<Self, Self::Error> {
        match value {
            0x01 => Ok(Command::Connect),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "unexpected command {value}",
            )),
        }
    }
}