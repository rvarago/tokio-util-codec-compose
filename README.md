# tokio-util-codec-compose

[![Check](https://github.com/rvarago/tokio-util-codec-compose/actions/workflows/check.yml/badge.svg)](https://github.com/rvarago/tokio-util-codec-compose/actions/workflows/check.yml)

A Rust library with building blocks for composing [tokio-util](https://docs.rs/tokio-util/latest/tokio_util) codecs

> This library was inspired by [scodec](https://github.com/scodec/scodec).

## Overview

Decoding communication protocols from byte streams usually involves the combination of multiple steps, e.g. decode the header and then the payload. Also, decoders often have state, e.g. we have multiple decoders for the payload where we select the appropriate one based on the header.

However, we may find ourselves repeating the same sequence of decoding steps multiple times and possibly judging their correctness only as part of a larger sequence, not in terms of the individual steps; again multiple times.

To tackle this, `tokio-util-codec-compose` library builds atop the great `tokio-util` and encapsulates some patterns I have seen when implementing codecs for communication protocols, for both stateless and stateful protocols.

## Features

- Primitives to decode sequences of bytes into data-types
- Operations to compose simpler decoders into more powerful ones

## Roadmap

- Add more combinators
- Add support for encoding, e.g. `contra_map`
- Flatten nested tuples

## Examples

### Decoding

Conceptually, you can think of a `Decoder<Item = T>` as an `Option<T>` in the sense that you can
`map` it, sequence it with an `and_then`, etc. That with an extra twist:
decoders can carry state around while decoding a frame, e.g. wait for `N` bytes, then decide whether to read `M` or `Q` bytes, and so on. This might translate
into a state-machine which explicitly state tracking, which may get tedious.

For some decoding patterns, you can leverage the compositional operations provided by this library, you can build complex decoders
out of simpler building blocks that you can develop, test, and reason about, in isolation.

Decoding a SOCKS v4 CONNECT request with no validation interleaved with decoding:

```rust
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

    // SOCKS v4 request to CONNECT "Fred" to 66.102.7.99:80
    let mut src = BytesMut::from("\x04\x01\x00\x50\x42\x66\x07\x63\x46\x72\x65\x64\x00");
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
```

See more [examples](./examples).

## Contributing

Contributions are more than welcome! If you encounter any issue, have feature requests, or want to make improvements, please open an issue or submit a pull request.

## License

This library is licensed under the MIT License. Please refer to the [LICENSE](./LICENSE) file for more information.
