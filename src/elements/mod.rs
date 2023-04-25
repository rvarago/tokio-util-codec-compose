//! Building blocks for composing codecs.

pub mod ints;

use super::combinators::DecoderExt;

use std::{io, net::Ipv4Addr};
use tokio_util::codec::Decoder;

/// Shorthand notation to construct an [`ints::U8`].
pub fn uint8() -> ints::U8 {
    ints::U8::default()
}

/// Shorthand notation to construct an [`ints::U16BE`].
pub fn uint16_be() -> ints::U16BE {
    ints::U16BE::default()
}

/// Shorthand notation to construct an [`ints::U16LE`].
pub fn uint16_le() -> ints::U16LE {
    ints::U16LE::default()
}

/// Shorthand notation to construct an [`ints::U32BE`].
pub fn uint32_be() -> ints::U32BE {
    ints::U32BE::default()
}

/// Shorthand notation to construct an [`ints::U32LE`].
pub fn uint32_le() -> ints::U32LE {
    ints::U32LE::default()
}

/// Codec for an [`Ipv4Addr`] as a sequence of four contiguous [`u8`].
///
/// # Examples
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Decoder;
/// # use tokio_util_codec_compose::elements::ipv4;
/// let mut decoder = ipv4();
///
/// let res = decoder.decode(&mut BytesMut::from("\x42\x66\x07\x63")).unwrap();
///
/// assert_eq!(res, "66.102.7.99".parse().ok())
/// ```
pub fn ipv4() -> impl Decoder<Item = Ipv4Addr, Error = io::Error> {
    uint8()
        .then(uint8())
        .then(uint8())
        .then(uint8())
        .map(|(((a, b), c), d)| Ipv4Addr::new(a, b, c, d))
}
