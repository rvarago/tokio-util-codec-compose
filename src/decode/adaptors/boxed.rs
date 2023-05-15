//! An adaptor for boxing decoders.

use bytes::BytesMut;
use std::io;
use tokio_util::codec::Decoder;

/// A decoder that boxes another decoder.
///
/// The result of [`crate::decode::DecoderExt::boxed`].
#[must_use = "decoders do nothing unless used"]
pub struct DecoderBoxed<A, E> {
    inner: Box<dyn Decoder<Item = A, Error = E>>,
}

impl<A, E> DecoderBoxed<A, E> {
    pub(in crate::decode) fn new<D>(inner: D) -> Self
    where
        D: Decoder<Item = A, Error = E>,
        D: 'static,
    {
        Self {
            inner: Box::new(inner),
        }
    }
}

impl<A, E> Decoder for DecoderBoxed<A, E>
where
    E: From<io::Error>,
{
    type Item = A;

    type Error = E;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        self.inner.decode(src)
    }
}
