//! Composition operations on [`Decoder`].

use bytes::BytesMut;
use std::{io, marker::PhantomData};
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

    /// Chains a decoder of `B` on the *remaining* bytes after applying this decoder, then returns a pair of the individual outcomes `(a, b)`.
    ///
    /// This enables the application of decoders in sequence where a step does not depend on its predecessor (when such a dependency exists, consider [`DecoderExt::and_then`].
    ///
    /// The next decoder can return an error type `EE` other than `E` as long as there is an implicit conversion [`From<E>`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use tokio_util::codec::Decoder;
    /// # use bytes::{BytesMut, Buf};
    /// use tokio_util_codec_compose::{combinators::DecoderExt, elements::uint8};
    ///
    /// # #[derive(Debug, PartialEq, Eq)]
    /// struct Device(u8, u8);
    ///
    /// let device = uint8().then(uint8()).map(|(a, b)| Device(a, b)).decode(&mut BytesMut::from("\x2A\x3B")).unwrap();
    ///
    /// assert_eq!(device, Some(Device(0x2A, 0x3B)));
    /// ```
    fn then<DNext, B, EE>(self, next: DNext) -> DecoderThen<Self, DNext, EE>
    where
        DNext: Decoder<Item = B, Error = EE>,
        EE: From<E>,
        Self: Sized;

    /// Chains a function `f` of type `A -> Box<Decoder<Item = B, Error = E>>` over the decoded value when that is `Ok(Some(a))`.
    ///
    /// Contrary to [`DecoderExt::map`], the function `f` can decide (dynamically) which decoder to return next according to `a`, which enables complex behaviors
    /// out of simple building blocks by defining dependency relationships between decoders.
    /// e.g. first we decode the header of a message and use that information, say protocol version, to then select the appropriate
    /// decoder among multiple candidates, say one per protocol version, for the body.
    ///
    /// The next decoder can return an error type `EE` other than `E` as long as there is an implicit conversion [`From<E>`].
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
    fn and_then<F, B, EE>(self, f: F) -> DecoderAndThen<Self, F, EE>
    where
        F: Fn(A) -> Box<dyn Decoder<Item = B, Error = EE>>,
        F: 'static,
        EE: From<E>,
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

    fn and_then<F, B, EE>(self, f: F) -> DecoderAndThen<Self, F, EE>
    where
        F: Fn(A) -> Box<dyn Decoder<Item = B, Error = EE>>,
        F: 'static,
        EE: From<E>,
        Self: Sized,
    {
        DecoderAndThen {
            inner: self,
            f,
            _error: PhantomData,
        }
    }

    fn then<DNext, B, EE>(self, next: DNext) -> DecoderThen<Self, DNext, EE>
    where
        DNext: Decoder<Item = B, Error = EE>,
        EE: From<E>,
        Self: Sized,
    {
        DecoderThen {
            first: self,
            second: next,
            _error: PhantomData,
        }
    }
}

#[derive(Debug)]
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

#[derive(Debug)]
pub struct DecoderAndThen<D, F, E> {
    inner: D,
    f: F,
    _error: PhantomData<E>,
}

impl<D, F, A, B, EA, EB, EE> Decoder for DecoderAndThen<D, F, EE>
where
    D: Decoder<Item = A, Error = EA>,
    F: Fn(A) -> Box<dyn Decoder<Item = B, Error = EB>>,
    EA: From<io::Error>,
    EB: From<io::Error>,
    EE: From<io::Error> + From<EA> + From<EB>,
{
    type Item = B;

    type Error = EE;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        Ok(self
            .inner
            .decode(src)?
            .and_then(|a| (self.f)(a).decode(src).transpose())
            .transpose()?)
    }
}

#[derive(Debug)]
pub struct DecoderThen<DFirst, DSecond, E> {
    first: DFirst,
    second: DSecond,
    _error: PhantomData<E>,
}

impl<DFirst, DSecond, A, B, EA, EB, EE> Decoder for DecoderThen<DFirst, DSecond, EE>
where
    DFirst: Decoder<Item = A, Error = EA>,
    DSecond: Decoder<Item = B, Error = EB>,
    EA: From<io::Error>,
    EB: From<io::Error>,
    EE: From<io::Error> + From<EA> + From<EB>,
{
    type Item = (A, B);

    type Error = EE;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        let opta = self.first.decode(src)?;
        let optb = self.second.decode(src)?;

        Ok(opta.zip(optb))
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
