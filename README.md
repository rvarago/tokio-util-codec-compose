# tokio-util-codec-compose

[![Check](https://github.com/rvarago/tokio-util-codec-compose/actions/workflows/check.yml/badge.svg)](https://github.com/rvarago/tokio-util-codec-compose/actions/workflows/check.yml)

A Rust library with building blocks for composing [tokio-util](https://docs.rs/tokio-util/latest/tokio_util) codecs

> This library was inspired by [scodec](https://github.com/scodec/scodec).

## Overview

Decoding communication protocols from byte streams usually involves the combination of multiple steps, e.g. decode the header and then the payload. Also, decoders often have state, e.g. we have multiple decoders for the payload where we select the appropriate one based on the header.

However, we may find ourselves repeating the same sequence of decoding steps multiple times and possibly judging their correctness only as part of larger sequence, not in terms of the individual steps; again multiple times.

To tackle this, `tokio-util-codec-compose` library builds atop the great `tokio-util` and encapsulates some patterns I have seen when implementing codecs for communications protocols, for both stateless and stateful protocols.

## Features

- Primitives to decode sequences of bytes into data-types
- Operations to compose simpler decoders into more powerful ones

## Roadmap

- Add more combinators
- Add support for encoding
- Flatten nested tuples

## Examples

Decoding a SOCKS v4 CONNECT request with no validation interleaved with decoding:

```rust
use tokio_util_codec_compose::{combinators::DecoderExt, elements::*};

use anyhow::Result;
use bytes::BytesMut;
use std::net::Ipv4Addr;
use tokio_util::codec::Decoder;

fn main() -> Result<()> {
    let mut decoder = socks_request_decoder();

    // SOCKS v4 request to CONNECT "Fred" to 66.102.7.99:80
    let mut src = BytesMut::from("\x04\x01\x00\x50\x42\x66\x07\x63\x46\x72\x65\x64\x00");
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

    Ok(())
}

fn socks_request_decoder() -> impl Decoder<Item = SocksRequest, Error = anyhow::Error> {
    uint8()
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
        )
        .map_err(|e| anyhow::format_err!("could not decode socks request, reason: {e}"))
}

#[derive(Debug, PartialEq, Eq)]
struct SocksRequest {
    version: u8,
    command: u8,
    destination_port: u16,
    destination_ip: Ipv4Addr,
    user_id: String,
}
```

See more [examples](./examples).

## Contributing

Contributions are more than welcome! If you encounter any issue, have feature requests, or want to make improvements, please open an issue or submit a pull request.

## License

This library is licensed under the MIT License. Please refer to the [LICENSE](./LICENSE) file for more information.
