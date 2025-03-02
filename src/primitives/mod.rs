//! Building blocks for with simple decoding/encoding primitives.

pub mod ints;

use crate::decode::DecoderExt;

use bytes::Bytes;
use std::{io, net::Ipv4Addr};
use tokio_util::codec::Decoder;

/// Shorthand to construct an [`ints::U8`].
pub fn uint8() -> ints::U8 {
    ints::U8
}

/// Shorthand to construct an [`ints::U16BE`].
pub fn uint16_be() -> ints::U16BE {
    ints::U16BE
}

/// Shorthand to construct an [`ints::U16LE`].
pub fn uint16_le() -> ints::U16LE {
    ints::U16LE
}

/// Shorthand to construct an [`ints::U32BE`].
pub fn uint32_be() -> ints::U32BE {
    ints::U32BE
}

/// Shorthand to construct an [`ints::U32LE`].
pub fn uint32_le() -> ints::U32LE {
    ints::U32LE
}

/// Decoder for an [`Ipv4Addr`] as a sequence of four contiguous [`u8`].
///
/// # Examples
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Decoder;
/// # use tokio_util_codec_compose::primitives::ipv4;
/// let mut decoder = ipv4();
///
/// let res = decoder.decode(&mut BytesMut::from("\x42\x66\x07\x63")).unwrap();
///
/// assert_eq!(res, "66.102.7.99".parse().ok())
/// ```
#[must_use = "decoders do nothing unless used"]
pub fn ipv4() -> impl Decoder<Item = Ipv4Addr, Error = io::Error> {
    uint8()
        .then(uint8())
        .then(uint8())
        .then(uint8())
        .map(|(((a, b), c), d)| Ipv4Addr::new(a, b, c, d))
}

/// Shorthand to construct a decoder delimited by `seek_delimiters` up to length `max_length`.
///
/// Delegates to [`tokio_util::codec::AnyDelimiterCodec`].
#[must_use = "decoders do nothing unless used"]
pub fn delimited_by(
    seek_delimiters: impl Into<Vec<u8>>,
    max_lenght: usize,
) -> impl Decoder<Item = Bytes, Error = tokio_util::codec::AnyDelimiterCodecError> {
    tokio_util::codec::AnyDelimiterCodec::new_with_max_length(
        seek_delimiters.into(),
        Vec::default(),
        max_lenght,
    )
}
