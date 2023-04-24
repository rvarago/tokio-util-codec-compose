//! Codecs of integers.

use bytes::Buf;

/// Codec for [`u8`].
///
/// # Examples
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Decoder;
/// # use tokio_util_codec_compose::elements::ints::U8;
/// let mut decoder = U8::default();
///
/// let res = decoder.decode(&mut BytesMut::from("\x2A")).unwrap();
///
/// assert_eq!(res, Some(42))
/// ```
#[derive(Debug, Default)]
pub struct U8;

/// Codec for [`u16`] little-endian.
///
/// # Examples
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Decoder;
/// # use tokio_util_codec_compose::elements::ints::U16LE;
/// let mut decoder = U16LE::default();
///
/// let res = decoder.decode(&mut BytesMut::from("\x2A\x3B")).unwrap();
///
/// assert_eq!(res, Some(0x3B2A))
/// ```
#[derive(Debug, Default)]
pub struct U16LE;

/// Codec for [`u16`] big-endian.
///
/// # Examples
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Decoder;
/// # use tokio_util_codec_compose::elements::ints::U16BE;
/// let mut decoder = U16BE::default();
///
/// let res = decoder.decode(&mut BytesMut::from("\x2A\x3B")).unwrap();
///
/// assert_eq!(res, Some(0x2A3B))
/// ```
#[derive(Debug, Default)]
pub struct U16BE;

/// Codec for [`u32`] little-endian.
///
/// # Examples
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Decoder;
/// # use tokio_util_codec_compose::elements::ints::U32LE;
/// let mut decoder = U32LE::default();
///
/// let res = decoder.decode(&mut BytesMut::from("\x2A\x3B\x4C\x5D")).unwrap();
///
/// assert_eq!(res, Some(0x5D4C3B2A))
/// ```
#[derive(Debug, Default)]
pub struct U32LE;

/// Codec for [`u32`] big-endian.
///
/// # Examples
///
/// ```
/// # use bytes::BytesMut;
/// # use tokio_util::codec::Decoder;
/// # use tokio_util_codec_compose::elements::ints::U32BE;
/// let mut decoder = U32BE::default();
///
/// let res = decoder.decode(&mut BytesMut::from("\x2A\x3B\x4C\x5D")).unwrap();
///
/// assert_eq!(res, Some(0x2A3B4C5D))
/// ```
#[derive(Debug, Default)]
pub struct U32BE;

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
impl_decoder!(U16LE, u16, 2, get_u16_le);
impl_decoder!(U16BE, u16, 2, get_u16);
impl_decoder!(U32LE, u32, 4, get_u32_le);
impl_decoder!(U32BE, u32, 4, get_u32);

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;
    use bytes::BytesMut;
    use tokio_util::codec::Decoder;

    #[test]
    fn u8_decode() -> Result<()> {
        let mut decoder = U8::default();
        let mut src = BytesMut::from("\x2A\x00\x01\x02\x03");

        let res = decoder.decode(&mut src)?;

        assert_eq!(res, Some(0x2A));
        assert_eq!(src, BytesMut::from("\x00\x01\x02\x03"));

        Ok(())
    }

    #[test]
    fn u16le_decode() -> Result<()> {
        let mut decoder = U16LE::default();
        let mut src = BytesMut::from("\x2A\x3B\x01\x02\x03");

        let res = decoder.decode(&mut src)?;

        assert_eq!(res, Some(0x3B2A));
        assert_eq!(src, BytesMut::from("\x01\x02\x03"));

        Ok(())
    }

    #[test]
    fn u16be_decode() -> Result<()> {
        let mut decoder = U16BE::default();
        let mut src = BytesMut::from("\x2A\x3B\x01\x02\x03");

        let res = decoder.decode(&mut src)?;

        assert_eq!(res, Some(0x2A3B));
        assert_eq!(src, BytesMut::from("\x01\x02\x03"));

        Ok(())
    }
}
