//! Codecs of integers.

use bytes::{Buf, BytesMut};
use std::io;
use tokio_util::codec::Decoder;

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

impl Decoder for U8 {
    type Item = u8;

    type Error = io::Error;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        if src.len() < 1 {
            Ok(None)
        } else {
            Ok(src.get_u8().into())
        }
    }
}

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

impl Decoder for U16LE {
    type Item = u16;

    type Error = io::Error;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        if src.len() < 2 {
            Ok(None)
        } else {
            Ok(src.get_u16_le().into())
        }
    }
}

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

impl Decoder for U16BE {
    type Item = u16;

    type Error = io::Error;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        if src.len() < 2 {
            Ok(None)
        } else {
            Ok(src.get_u16().into())
        }
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use super::*;

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
