//! An adaptor for non-fallible mappings.

use bytes::BytesMut;
use std::io;
use tokio_util::codec::Encoder;

/// An encoder for applying a non-fallible transformation.
///
/// The result of [`crate::encode::combinators::EncoderExt::contra_map`].
#[must_use = "encoders do nothing unless used"]
#[derive(Debug)]
pub struct EncoderContraMap<C, F> {
    inner: C,
    f: F,
}

impl<C, F> EncoderContraMap<C, F> {
    pub(in crate::encode::combinators) fn new(inner: C, f: F) -> Self {
        Self { inner, f }
    }
}

impl<C, F, A, B, E> Encoder<B> for EncoderContraMap<C, F>
where
    C: Encoder<A, Error = E>,
    F: Fn(B) -> A,
    E: From<io::Error>,
{
    type Error = E;

    fn encode(&mut self, item: B, dst: &mut BytesMut) -> Result<(), Self::Error> {
        self.inner.encode((self.f)(item), dst)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encode::combinators::EncoderExt;
    use bytes::BufMut;

    #[test]
    fn encode_contra_map() -> anyhow::Result<()> {
        let mut encoder = U8::default().contra_map(|d: Device| d.0);

        let mut dst = BytesMut::default();
        encoder.encode(Device(0x01), &mut dst)?;

        assert_eq!(dst, BytesMut::from("\x01"));

        Ok(())
    }

    #[derive(Debug, PartialEq, Eq)]
    struct Device(u8);

    #[derive(Debug, Default, PartialEq, Eq)]
    struct U8(u8);

    impl Encoder<u8> for U8 {
        type Error = io::Error;

        fn encode(&mut self, item: u8, dst: &mut BytesMut) -> Result<(), Self::Error> {
            dst.reserve(1);
            dst.put_u8(item);
            Ok(())
        }
    }
}
