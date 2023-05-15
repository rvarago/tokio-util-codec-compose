//! An adaptor for non-fallible mappings.

use bytes::BytesMut;
use std::io;
use tokio_util::codec::Decoder;

/// A decoder for applying a non-fallible transformation on the success type.
///
/// The result of [`crate::decode::DecoderExt::map`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderMap<D, F> {
    inner: D,
    f: F,
}

impl<D, F> DecoderMap<D, F> {
    pub(in crate::decode) fn new(inner: D, f: F) -> Self {
        Self { inner, f }
    }
}

impl<D, F, A, B, E> Decoder for DecoderMap<D, F>
where
    D: Decoder<Item = A, Error = E>,
    F: Fn(A) -> B,
    E: From<io::Error>,
{
    type Item = B;

    type Error = E;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        Ok(self.inner.decode(src)?.map(&self.f))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{decode::DecoderExt, primitives::uint8};

    use proptest::prelude::*;
    use std::{convert::identity as id, fmt::Debug};
    use tokio_util::codec::BytesCodec;

    // TODO: Check laws.

    proptest! {
        #[test]
        fn decode_map_check_law_map_id(src in bytes()) {
            // TODO: Generate multiple decoders synced with valid byte-sequences with success/failure.
            let src = BytesMut::from(src.as_slice());
            let decoder = BytesCodec::default();
            decode_map_law_map_id_succeed(decoder, src);
        }
    }

    #[track_caller]
    fn decode_map_law_map_id_succeed<D, A, E>(mut decoder: D, mut src: BytesMut)
    where
        D: Decoder<Item = A, Error = E> + Clone,
        A: PartialEq + Debug,
        E: Debug + From<io::Error>,
    {
        let mut src_mapped = src.clone();
        let mut decoder_mapped = decoder.clone().map(id);

        let res = decoder.decode(&mut src).unwrap();
        let res_mapped = decoder_mapped.decode(&mut src_mapped).unwrap();

        assert_eq!(res, res_mapped);
        assert_eq!(src, src_mapped);
    }

    fn bytes() -> impl Strategy<Value = Vec<u8>> {
        proptest::collection::vec(any::<u8>(), 0..255)
    }

    #[test]
    fn decode_map() -> anyhow::Result<()> {
        let mut decoder = uint8().map(Device);

        let mut src = BytesMut::from("\x01");
        let value = decoder.decode(&mut src)?;

        assert!(matches!(value, Some(Device(0x01))));
        assert_eq!(src, BytesMut::default());

        Ok(())
    }

    #[derive(Debug, PartialEq, Eq)]
    struct Device(u8);
}
