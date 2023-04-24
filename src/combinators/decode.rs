//! Composition operations on [`Decoder`].

use bytes::BytesMut;
use std::io;
use tokio_util::codec::Decoder;

pub trait DecoderExt<A, E> {
    /// Applies a function `f` of type `A -> B` over the decoded value when that is `Ok(Some(a))`.
    ///
    /// The function `f` cannot fail.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tokio_util::codec::Decoder;
    /// # use bytes::{BytesMut, Buf};
    /// use tokio_util_codec_compose::{combinators::DecoderExt, elements::uint8};
    ///
    /// # #[derive(Debug, PartialEq, Eq)]
    /// struct Device(u8);
    ///
    /// let device = uint8().map(Device).decode(&mut BytesMut::from("\x2A")).unwrap();
    /// assert_eq!(device, Some(Device(42)));
    /// ```
    fn map<F, B>(self, f: F) -> DecoderMap<Self, F>
    where
        F: Fn(A) -> B,
        F: 'static,
        Self: Sized;

    /// Applies a function `f` of type `A -> Box<Decoder<Item = B, Error = E>>` over the decoded value when that is `Ok(Some(a))`.
    ///
    /// Contrary to [`map`], the function `f` can decide which decoder to return next according to `a`, which allows dynamic behaviors.
    ///
    /// The function `f` cannot fail.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tokio_util::codec::Decoder;
    /// # use bytes::{BytesMut, Buf};
    /// use tokio_util_codec_compose::{combinators::DecoderExt, elements::{uint8, uint16_be, uint16_le}};
    ///
    /// # #[derive(Debug, PartialEq, Eq)]
    /// struct Device(u16);
    ///
    /// fn payload_for_version(version: u8) -> Box<dyn Decoder<Item = u16, Error = std::io::Error>> {
    ///     if version == 0x01 { Box::new(uint16_be()) } else { Box::new(uint16_le()) }
    /// }
    ///
    /// let mut decoder = uint8().and_then(payload_for_version).map(Device);
    ///
    /// let device_big_endian = decoder.decode(&mut BytesMut::from("\x01\x2A\x3B")).unwrap();
    /// assert_eq!(device_big_endian, Some(Device(0x2A3B)));
    ///
    /// let device_little_endian = decoder.decode(&mut BytesMut::from("\x00\x2A\x3B")).unwrap();
    /// assert_eq!(device_little_endian, Some(Device(0x3B2A)));
    /// ```
    fn and_then<F, B>(self, f: F) -> DecoderAndThen<Self, F>
    where
        F: Fn(A) -> Box<dyn Decoder<Item = B, Error = E>>,
        F: 'static,
        Self: Sized;
}

impl<D, A, E> DecoderExt<A, E> for D
where
    D: Decoder<Item = A, Error = E>,
    D: 'static,
{
    fn map<F, B>(self, f: F) -> DecoderMap<Self, F>
    where
        F: Fn(A) -> B,
        F: 'static,
    {
        DecoderMap { inner: self, f }
    }

    fn and_then<F, B>(self, f: F) -> DecoderAndThen<Self, F>
    where
        F: Fn(A) -> Box<dyn Decoder<Item = B, Error = E>>,
        F: 'static,
        Self: Sized,
    {
        DecoderAndThen { inner: self, f }
    }
}

pub struct DecoderMap<D, F> {
    inner: D,
    f: F,
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

pub struct DecoderAndThen<D, F> {
    inner: D,
    f: F,
}

impl<D, F, A, B, E> Decoder for DecoderAndThen<D, F>
where
    D: Decoder<Item = A, Error = E>,
    F: Fn(A) -> Box<dyn Decoder<Item = B, Error = E>>,
    E: From<io::Error>,
{
    type Item = B;

    type Error = E;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        self.inner
            .decode(src)?
            .and_then(|a| (self.f)(a).decode(src).transpose())
            .transpose()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use std::{convert::identity as id, fmt::Debug};
    use tokio_util::codec::BytesCodec;

    // TODO: Check composition law.
    // TODO: Add more test-cases.

    proptest! {
        #[test]
        fn check_law_map_id(src in bytes()) {
            // TODO: Generate multiple decoders synced with valid byte-sequences with success/failure.
            let src = BytesMut::from(src.as_slice());
            let decoder = BytesCodec::default();
            law_map_id_succeed(decoder, src);
        }
    }

    #[track_caller]
    fn law_map_id_succeed<D, A, E>(mut decoder: D, mut src: BytesMut)
    where
        D: Decoder<Item = A, Error = E> + Clone + 'static,
        A: PartialEq + Debug + 'static,
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
}
