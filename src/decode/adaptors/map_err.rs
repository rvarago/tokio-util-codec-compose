//! An adaptor for non-fallible mappings over errors.

use bytes::BytesMut;
use std::io;
use tokio_util::codec::Decoder;

/// A decoder for applying a fallible transformation on the error type.
///
/// The result of [`crate::decode::DecoderExt::map_err`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderMapErr<D, F> {
    inner: D,
    f: F,
}

impl<D, F> DecoderMapErr<D, F> {
    pub(in crate::decode) fn new(inner: D, f: F) -> Self {
        Self { inner, f }
    }
}

impl<D, F, A, E, EE> Decoder for DecoderMapErr<D, F>
where
    D: Decoder<Item = A, Error = E>,
    F: Fn(E) -> EE,
    E: From<io::Error>,
    EE: From<io::Error>,
{
    type Item = A;

    type Error = EE;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        self.inner.decode(src).map_err(&self.f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{decode::DecoderExt, primitives::uint8};

    #[test]
    fn decode_map_err_succeed() {
        let mut decoder = uint8()
            .try_map(|_| Ok::<_, io::Error>(0x42))
            .map_err(DecodeMapErrError::from);

        let mut src = BytesMut::from("\x01");
        let ok = decoder.decode(&mut src);

        assert_eq!(ok, Ok(Some(0x42)));
        assert_eq!(src, BytesMut::default());
    }

    #[test]
    fn decode_map_err_fail() {
        let mut decoder = uint8()
            .try_map(|_| Err::<u8, _>(io::Error::from(io::ErrorKind::Other)))
            .map_err(|e| DecodeMapErrError {
                kind: e.kind(),
                msg: "no particular reason".into(),
            });

        let mut src = BytesMut::from("\x01");
        let ok = decoder.decode(&mut src);

        assert_eq!(
            ok,
            Err(DecodeMapErrError {
                kind: io::ErrorKind::Other,
                msg: Some("no particular reason")
            })
        );
        assert_eq!(src, BytesMut::default());
    }

    #[derive(Debug, PartialEq, Eq)]
    struct DecodeMapErrError {
        kind: io::ErrorKind,
        msg: Option<&'static str>,
    }

    impl From<io::Error> for DecodeMapErrError {
        fn from(value: io::Error) -> Self {
            Self {
                kind: value.kind(),
                msg: None,
            }
        }
    }
}
