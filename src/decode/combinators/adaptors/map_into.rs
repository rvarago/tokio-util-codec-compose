//! An adaptor for non-fallible mappings with implicit conversions.

use bytes::BytesMut;
use std::{io, marker::PhantomData};
use tokio_util::codec::Decoder;

/// A decoder for applying a non-fallible conversion onto the success type.
///
/// The result of [`crate::decode::combinators::DecoderExt::map_into`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderMapInto<D, B> {
    inner: D,
    _target: PhantomData<B>,
}

impl<D, B> DecoderMapInto<D, B> {
    pub(in crate::decode::combinators) fn new(inner: D) -> Self {
        Self {
            inner,
            _target: PhantomData,
        }
    }
}

impl<D, A, B, E> Decoder for DecoderMapInto<D, B>
where
    D: Decoder<Item = A, Error = E>,
    B: From<A>,
    E: From<io::Error>,
{
    type Item = B;

    type Error = E;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        Ok(self.inner.decode(src)?.map(B::from))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::decode::{combinators::DecoderExt, primitives::uint8};

    #[test]
    fn decode_map_into() -> anyhow::Result<()> {
        #[derive(Debug, PartialEq, Eq)]
        struct Device(u8);
        impl From<u8> for Device {
            fn from(value: u8) -> Self {
                Self(value)
            }
        }
        let mut decoder = uint8().map_into::<Device>();

        let mut src = BytesMut::from("\x01");
        let value = decoder.decode(&mut src)?;

        assert!(matches!(value, Some(Device(0x01))));
        assert_eq!(src, BytesMut::default());

        Ok(())
    }
}
