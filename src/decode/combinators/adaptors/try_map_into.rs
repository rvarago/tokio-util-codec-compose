//! An adaptor for fallible mappings with implicit conversions.

use bytes::BytesMut;
use std::{io, marker::PhantomData};
use tokio_util::codec::Decoder;

/// A decoder for applying a fallible conversion onto the success type.
///
/// The result of [`crate::decode::combinators::DecoderExt::try_map_into`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderTryMapInto<D, B, E> {
    inner: D,
    _target: PhantomData<B>,
    _error: PhantomData<E>,
}

impl<D, B, E> DecoderTryMapInto<D, B, E> {
    pub(in crate::decode::combinators) fn new(inner: D) -> Self {
        Self {
            inner,
            _target: PhantomData,
            _error: PhantomData,
        }
    }
}

impl<D, A, B, E, EE> Decoder for DecoderTryMapInto<D, B, EE>
where
    D: Decoder<Item = A, Error = E>,
    B: TryFrom<A, Error = EE>,
    E: From<io::Error>,
    EE: From<io::Error> + From<E>,
{
    type Item = B;

    type Error = EE;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        self.inner.decode(src)?.map(B::try_from).transpose()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::decode::{combinators::DecoderExt, primitives::uint8};

    #[test]
    fn decode_try_map_into_succeed() {
        let mut decoder = uint8().try_map_into::<Version>();

        let mut src = BytesMut::from("\x01");
        let ok = decoder.decode(&mut src);

        assert!(matches!(ok, Ok(Some(Version::V1))));
        assert_eq!(src, BytesMut::default());
    }

    #[test]
    fn decode_try_map_into_fail() {
        let mut decoder = uint8().try_map_into::<Version>();

        let mut src = BytesMut::from("\x02");
        let err = decoder.decode(&mut src);
        let err_kind = err.map_err(|e| e.kind());

        assert!(matches!(err_kind, Err(io::ErrorKind::InvalidData)));
        assert_eq!(src, BytesMut::default());
    }

    #[derive(Debug, PartialEq, Eq)]
    enum Version {
        V1,
    }

    impl TryFrom<u8> for Version {
        type Error = std::io::Error;

        fn try_from(value: u8) -> Result<Self, Self::Error> {
            match value {
                1 => Ok(Version::V1),
                _ => Err(std::io::Error::from(std::io::ErrorKind::InvalidData)),
            }
        }
    }
}
