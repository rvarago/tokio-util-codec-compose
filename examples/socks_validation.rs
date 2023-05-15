//! A SOCKS v4 decoder with validation interleaved with decoding.

use tokio_util_codec_compose::{
    decode::DecoderExt,
    primitives::{delimited_by, ipv4, uint16_be, uint8},
};

use anyhow::Result;
use bytes::BytesMut;
use std::{io, net::Ipv4Addr};
use tokio_util::codec::Decoder;

fn main() -> Result<()> {
    let mut decoder = socks_request_decoder();

    // SOCKS v4 invalid request (wrong version 0x05)

    let mut src = BytesMut::from("\x05");
    let res = decoder.decode(&mut src);

    assert!(res.is_err());

    // SOCKS v4 valid request to CONNECT "Fred" to 66.102.7.99:80

    // Only a few bytes are available
    let mut src = BytesMut::from("\x04\x01");
    let res = decoder.decode(&mut src)?;

    assert_eq!(res, None);
    assert_eq!(src, BytesMut::from(""));

    // The rest of the bytes
    let mut src = BytesMut::from("\x00\x50\x42\x66\x07\x63\x46\x72\x65\x64\x00");
    let res = decoder.decode(&mut src)?;

    assert_eq!(
        Some(SocksRequest {
            version: Version::V4,
            command: Command::Connect,
            destination_port: Port(80),
            destination_ip: "66.102.7.99".parse()?,
            user_id: "Fred".into(),
        }),
        res
    );
    assert_eq!(src, BytesMut::from(""));

    dbg!(res);

    Ok(())
}

fn socks_request_decoder() -> impl Decoder<Item = SocksRequest, Error = anyhow::Error> {
    version()
        .then(command())
        .then(port())
        .then(ipv4())
        .then(user_id())
        .map(from_parts)
        .map_err(|e| anyhow::format_err!("could not decode socks request, reason: {e}"))
}

fn version() -> impl Decoder<Item = Version, Error = io::Error> {
    uint8().try_map_into()
}

fn command() -> impl Decoder<Item = Command, Error = io::Error> {
    uint8().try_map_into()
}

fn port() -> impl Decoder<Item = Port, Error = io::Error> {
    uint16_be().map_into()
}

fn user_id() -> impl Decoder<Item = String, Error = tokio_util::codec::AnyDelimiterCodecError> {
    delimited_by([b'\x00'], 255).map(|bytes| String::from_utf8_lossy(&bytes).into_owned())
}

type SocksRequestParts = ((((Version, Command), Port), Ipv4Addr), String);

fn from_parts(
    ((((version, command), destination_port), destination_ip), user_id): SocksRequestParts,
) -> SocksRequest {
    SocksRequest {
        version,
        command,
        destination_port,
        destination_ip,
        user_id,
    }
}

#[derive(Debug, PartialEq, Eq)]
struct SocksRequest {
    version: Version,
    command: Command,
    destination_port: Port,
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

#[derive(Debug, PartialEq, Eq)]
struct Port(u16);

impl From<u16> for Port {
    fn from(value: u16) -> Self {
        Port(value)
    }
}
