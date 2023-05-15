//! An adaptor for fallible mappings.

use bytes::BytesMut;
use std::{io, marker::PhantomData};
use tokio_util::codec::Decoder;

/// A decoder for applying a fallible transformation on the success type.
///
/// The result of [`crate::decode::DecoderExt::try_map`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderTryMap<D, F, E> {
    inner: D,
    f: F,
    _error: PhantomData<E>,
}

impl<D, F, E> DecoderTryMap<D, F, E> {
    pub(in crate::decode) fn new(inner: D, f: F) -> Self {
        Self {
            inner,
            f,
            _error: PhantomData,
        }
    }
}

impl<D, F, A, B, E, EE> Decoder for DecoderTryMap<D, F, EE>
where
    D: Decoder<Item = A, Error = E>,
    F: Fn(A) -> Result<B, EE>,
    E: From<io::Error>,
    EE: From<io::Error> + From<E>,
{
    type Item = B;

    type Error = EE;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        self.inner.decode(src)?.map(&self.f).transpose()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{decode::DecoderExt, primitives::uint8};

    #[test]
    fn decode_try_map_succeed() {
        let mut decoder = uint8().try_map(|_| Ok::<_, io::Error>(0x02u8));

        let mut src = BytesMut::from("\x01");
        let ok = decoder.decode(&mut src);

        assert!(matches!(ok, Ok(Some(0x02))));
        assert_eq!(src, BytesMut::default());
    }

    #[test]
    fn decode_try_map_fail() {
        let mut decoder = uint8().try_map(|_| Err::<u8, _>(io::Error::from(io::ErrorKind::Other)));

        let mut src = BytesMut::from("\x01");
        let err = decoder.decode(&mut src);
        let err_kind = err.map_err(|e| e.kind());

        assert!(matches!(err_kind, Err(io::ErrorKind::Other)));
        assert_eq!(src, BytesMut::default());
    }
}
