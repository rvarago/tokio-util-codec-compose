//! Codec for integers.

use bytes::{Buf, BufMut};

/// Codec for an [`u8`].
///
/// # Examples
///
/// ## Decoding
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Decoder;
/// # use tokio_util_codec_compose::primitives::ints::U8;
/// let mut decoder = U8::default();
///
/// let res = decoder.decode(&mut BytesMut::from("\x2A")).unwrap();
///
/// assert_eq!(res, Some(42))
/// ```
///
/// ## Encoding
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Encoder;
/// # use tokio_util_codec_compose::primitives::ints::U8;
/// let mut encoder = U8::default();
///
/// let mut dst = BytesMut::default();
/// encoder.encode(0x2A, &mut dst).unwrap();
///
/// assert_eq!(dst, BytesMut::from("\x2A"))
/// ```
#[must_use = "decoders do nothing unless used"]
#[derive(Debug, Default)]
pub struct U8;

/// Codec for an [`u16`] big-endian.
///
/// # Examples
///
/// ## Decoding
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Decoder;
/// # use tokio_util_codec_compose::primitives::ints::U16BE;
/// let mut decoder = U16BE::default();
///
/// let res = decoder.decode(&mut BytesMut::from("\x2A\x3B")).unwrap();
///
/// assert_eq!(res, Some(0x2A3B))
/// ```
///
/// ## Encoding
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Encoder;
/// # use tokio_util_codec_compose::primitives::ints::U16BE;
/// let mut encoder = U16BE::default();
///
/// let mut dst = BytesMut::default();
/// encoder.encode(0x2A3B, &mut dst).unwrap();
///
/// assert_eq!(dst, BytesMut::from("\x2A\x3B"))
/// ```
#[must_use = "codecs do nothing unless used"]
#[derive(Debug, Default)]
pub struct U16BE;

/// Codec for an [`u16`] little-endian.
///
/// # Examples
///
/// ## Decoding
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Decoder;
/// # use tokio_util_codec_compose::primitives::ints::U16LE;
/// let mut decoder = U16LE::default();
///
/// let res = decoder.decode(&mut BytesMut::from("\x2A\x3B")).unwrap();
///
/// assert_eq!(res, Some(0x3B2A))
/// ```
///
/// ## Encoding
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Encoder;
/// # use tokio_util_codec_compose::primitives::ints::U16LE;
/// let mut encoder = U16LE::default();
///
/// let mut dst = BytesMut::default();
/// encoder.encode(0x2A3B, &mut dst).unwrap();
///
/// assert_eq!(dst, BytesMut::from("\x3B\x2A"))
/// ```
#[must_use = "codecs do nothing unless used"]
#[derive(Debug, Default)]
pub struct U16LE;

/// Codec for an [`u32`] big-endian.
///
/// # Examples
///
/// ## Decoding
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Decoder;
/// # use tokio_util_codec_compose::primitives::ints::U32BE;
/// let mut decoder = U32BE::default();
///
/// let res = decoder.decode(&mut BytesMut::from("\x2A\x3B\x4C\x5D")).unwrap();
///
/// assert_eq!(res, Some(0x2A3B4C5D))
/// ```
///
/// ## Encoding
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Encoder;
/// # use tokio_util_codec_compose::primitives::ints::U32BE;
/// let mut encoder = U32BE::default();
///
/// let mut dst = BytesMut::default();
/// encoder.encode(0x2A3B4C5D, &mut dst).unwrap();
///
/// assert_eq!(dst, BytesMut::from("\x2A\x3B\x4C\x5D"))
/// ```
#[must_use = "codecs do nothing unless used"]
#[derive(Debug, Default)]
pub struct U32BE;

/// Codec for an [`u32`] little-endian.
///
/// # Examples
///
/// ## Decoding
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Decoder;
/// # use tokio_util_codec_compose::primitives::ints::U32LE;
/// let mut decoder = U32LE::default();
///
/// let res = decoder.decode(&mut BytesMut::from("\x2A\x3B\x4C\x5D")).unwrap();
///
/// assert_eq!(res, Some(0x5D4C3B2A))
/// ```
///
/// ## Encoding
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Encoder;
/// # use tokio_util_codec_compose::primitives::ints::U32LE;
/// let mut encoder = U32LE::default();
///
/// let mut dst = BytesMut::default();
/// encoder.encode(0x5D4C3B2A, &mut dst).unwrap();
///
/// assert_eq!(dst, BytesMut::from("\x2A\x3B\x4C\x5D"))
/// ```
#[must_use = "codecs do nothing unless used"]
#[derive(Debug, Default)]
pub struct U32LE;

macro_rules! impl_decoder {
    ($type:ty, $value:ty, $len:expr, $get:ident) => {
        impl ::tokio_util::codec::Decoder for $type {
            type Item = $value;

            type Error = std::io::Error;

            fn decode(
                &mut self,
                src: &mut ::bytes::BytesMut,
            ) -> Result<Option<Self::Item>, Self::Error> {
                if src.len() < $len {
                    Ok(None)
                } else {
                    Ok(src.$get().into())
                }
            }
        }
    };
}

impl_decoder!(U8, u8, 1, get_u8);
impl_decoder!(U16BE, u16, 2, get_u16);
impl_decoder!(U16LE, u16, 2, get_u16_le);
impl_decoder!(U32BE, u32, 4, get_u32);
impl_decoder!(U32LE, u32, 4, get_u32_le);

macro_rules! impl_encoder {
    ($type:ty, $value:ty, $len:expr, $put:ident) => {
        impl ::tokio_util::codec::Encoder<$value> for $type {
            type Error = std::io::Error;

            fn encode(
                &mut self,
                item: $value,
                dst: &mut ::bytes::BytesMut,
            ) -> Result<(), Self::Error> {
                dst.reserve($len);
                dst.$put(item);
                Ok(())
            }
        }
    };
}

impl_encoder!(U8, u8, 1, put_u8);
impl_encoder!(U16BE, u16, 2, put_u16);
impl_encoder!(U16LE, u16, 2, put_u16_le);
impl_encoder!(U32BE, u32, 4, put_u32);
impl_encoder!(U32LE, u32, 4, put_u32_le);

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;
    use bytes::BytesMut;
    use std::{error, fmt::Debug};
    use tokio_util::codec::Decoder;

    #[test]
    fn u8_decode() -> Result<()> {
        check(CheckOpts {
            decoder: U8::default(),
            src: BytesMut::from("\x2A\x00\x01\x02\x03"),
            expected_output: 0x2A,
            expected_remainder: BytesMut::from("\x00\x01\x02\x03"),
        })
    }

    #[test]
    fn u16be_decode() -> Result<()> {
        check(CheckOpts {
            decoder: U16BE::default(),
            src: BytesMut::from("\x2A\x3B\x01\x02\x03"),
            expected_output: 0x2A3B,
            expected_remainder: BytesMut::from("\x01\x02\x03"),
        })
    }

    #[test]
    fn u16le_decode() -> Result<()> {
        check(CheckOpts {
            decoder: U16LE::default(),
            src: BytesMut::from("\x2A\x3B\x01\x02\x03"),
            expected_output: 0x3B2A,
            expected_remainder: BytesMut::from("\x01\x02\x03"),
        })
    }

    #[test]
    fn u32be_decode() -> Result<()> {
        check(CheckOpts {
            decoder: U32BE::default(),
            src: BytesMut::from("\x2A\x3B\x01\x02\x03"),
            expected_output: 0x2A3B_0102,
            expected_remainder: BytesMut::from("\x03"),
        })
    }

    #[test]
    fn u32le_decode() -> Result<()> {
        check(CheckOpts {
            decoder: U32LE::default(),
            src: BytesMut::from("\x2A\x3B\x01\x02\x03"),
            expected_output: 0x0201_3B2A,
            expected_remainder: BytesMut::from("\x03"),
        })
    }

    #[track_caller]
    fn check<D, A>(
        CheckOpts {
            mut decoder,
            mut src,
            expected_output,
            expected_remainder,
        }: CheckOpts<D, A>,
    ) -> Result<()>
    where
        D: Decoder<Item = A>,
        A: PartialEq + Debug,
        D::Error: error::Error + Send + Sync + 'static,
    {
        let output = decoder.decode(&mut src)?;

        assert_eq!(output, Some(expected_output));
        assert_eq!(src, expected_remainder);

        Ok(())
    }

    #[derive(Debug)]
    struct CheckOpts<D, A> {
        decoder: D,
        src: BytesMut,
        expected_output: A,
        expected_remainder: BytesMut,
    }
}
