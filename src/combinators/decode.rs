//! A set of structures and compositional operations on [`Decoder`].
//!
//! The operations take simpler decoders as inputs with customization functions and produce more powerful ones as output.

// TODO: Split structs into modules (once per file?).

use bytes::BytesMut;
use std::{io, marker::PhantomData};
use tokio_util::codec::Decoder;

/// Extension of [`Decoder`] with compositional operations.
pub trait DecoderExt<A, E>: Decoder<Item = A, Error = E> {
    /// Applies a function `f` of type `A -> B` over the decoded value when that is `Ok(Some(a))`.
    ///
    /// The function `f` cannot fail. If you need a fallible mapping, then consider [`DecoderExt::try_map`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use tokio_util::codec::Decoder;
    /// # use bytes::BytesMut;
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
        Self: Sized,
    {
        DecoderMap { inner: self, f }
    }

    /// Applies an [`B::from`] `A` conversion over the decoded value when that is `Ok(Some(a))`.
    ///
    /// The conversion cannot fail. If you need a fallible conversion, then consider [`DecoderExt::try_map_into`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use tokio_util::codec::Decoder;
    /// # use bytes::BytesMut;
    /// use tokio_util_codec_compose::{combinators::DecoderExt, elements::uint8};
    ///
    /// # #[derive(Debug, PartialEq, Eq)]
    /// struct Device(u8);
    ///
    /// impl From<u8> for Device {
    ///     fn from(value: u8) -> Self {
    ///         Self(value)
    ///     }
    /// }
    ///
    /// let device = uint8().map_into::<Device>().decode(&mut BytesMut::from("\x2A")).unwrap();
    /// assert_eq!(device, Some(Device(42)));
    /// ```
    fn map_into<B>(self) -> DecoderMapInto<Self, B>
    where
        B: From<A>,
        Self: Sized,
    {
        DecoderMapInto {
            inner: self,
            _target: PhantomData,
        }
    }

    /// Applies a fallible function `f` of type `A -> Result<B, EE>` over the decoded value when that is `Ok(Some(a))`.
    ///
    /// The function `f` can fail and that's handy when we interleave decoding with validation,
    /// for instance, when mapping from a larger domain (e.g. `u8`) into a smaller co-domain (e.g. `Version::v1`).
    /// If you don't need a fallible mapping, then consider [`DecoderExt::map`].
    ///
    /// The mapping can return an error type `EE` other than `E` as long as there is an implicit conversion [`From<E>`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use tokio_util::codec::Decoder;
    /// # use bytes::BytesMut;
    /// use tokio_util_codec_compose::{combinators::DecoderExt, elements::uint8};
    ///
    /// # #[derive(Debug, PartialEq, Eq)]
    /// enum Version {
    ///     V1
    /// }
    ///
    /// impl TryFrom<u8> for Version {
    ///     type Error = std::io::Error;
    ///
    ///     fn try_from(value: u8) -> Result<Self, Self::Error> {
    ///             match value {
    ///                 1 => Ok(Version::V1),
    ///                 _ => Err(std::io::Error::from(std::io::ErrorKind::InvalidData))
    ///             }
    ///     }
    /// }
    ///
    /// let mut decoder = uint8().try_map(Version::try_from);
    ///
    /// let version_ok = decoder.decode(&mut BytesMut::from("\x01")).unwrap();
    /// assert_eq!(version_ok, Some(Version::V1));
    ///
    /// let version_err = decoder.decode(&mut BytesMut::from("\x02")).unwrap_err();
    /// assert_eq!(version_err.kind(), std::io::ErrorKind::InvalidData);
    /// ```
    fn try_map<F, B, EE>(self, f: F) -> DecoderTryMap<Self, F, EE>
    where
        F: Fn(A) -> Result<B, EE>,
        Self: Sized,
    {
        DecoderTryMap {
            inner: self,
            f,
            _error: PhantomData,
        }
    }

    /// Applies an [`B::try_from`] `A` conversion over the decoded value when that is `Ok(Some(a))`.
    ///
    /// The conversion can fail and that's handy when we interleave decoding with validation,
    /// for instance, when mapping from a larger domain (e.g. `u8`) into a smaller co-domain (e.g. `Version::v1`).
    /// If you don't need a fallible conversion, then consider [`DecoderExt::map`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use tokio_util::codec::Decoder;
    /// # use bytes::BytesMut;
    /// use tokio_util_codec_compose::{combinators::DecoderExt, elements::uint8};
    ///
    /// # #[derive(Debug, PartialEq, Eq)]
    /// enum Version {
    ///     V1
    /// }
    ///
    /// impl TryFrom<u8> for Version {
    ///     type Error = std::io::Error;
    ///
    ///     fn try_from(value: u8) -> Result<Self, Self::Error> {
    ///             match value {
    ///                 1 => Ok(Version::V1),
    ///                 _ => Err(std::io::Error::from(std::io::ErrorKind::InvalidData))
    ///             }
    ///     }
    /// }
    ///
    /// let mut decoder = uint8().try_map_into::<Version>();
    ///
    /// let version_ok = decoder.decode(&mut BytesMut::from("\x01")).unwrap();
    /// assert_eq!(version_ok, Some(Version::V1));
    ///
    /// let version_err = decoder.decode(&mut BytesMut::from("\x02")).unwrap_err();
    /// assert_eq!(version_err.kind(), std::io::ErrorKind::InvalidData);
    /// ```
    fn try_map_into<B>(self) -> DecoderTryMapInto<Self, B, B::Error>
    where
        B: TryFrom<A>,
        Self: Sized,
    {
        DecoderTryMapInto {
            inner: self,
            _target: PhantomData,
            _error: PhantomData,
        }
    }

    /// Applies a function `f` of type `E -> EE` over the decoding error when that is `Err(e)`.
    ///
    /// That's handy when we need to adapt errors across boundaries.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tokio_util::codec::Decoder;
    /// # use bytes::BytesMut;
    /// use tokio_util_codec_compose::{combinators::DecoderExt, elements::uint8};
    ///
    /// fn decoder_operation() -> impl Decoder<Item = Operation, Error = std::io::Error> {
    /// #   uint8().try_map(|_| Err(std::io::Error::from(std::io::ErrorKind::Other)))
    /// }
    ///
    /// # #[derive(Debug, PartialEq, Eq)]
    /// enum Operation {
    ///     TurnOff, Turning
    /// }
    ///
    /// # #[derive(Debug, PartialEq, Eq)]
    /// struct OperationError;
    ///
    /// impl From<std::io::Error> for OperationError {
    ///     fn from(value: std::io::Error) -> Self {
    ///         Self
    ///     }
    /// }
    ///
    /// let err = decoder_operation().map_err(|_| OperationError).decode(&mut BytesMut::from("\x00")); // invalid operation number
    /// assert_eq!(err, Err(OperationError));
    /// ```
    fn map_err<F, EE>(self, f: F) -> DecoderMapErr<Self, F>
    where
        F: Fn(E) -> EE,
        Self: Sized,
    {
        DecoderMapErr { inner: self, f }
    }

    /// Chains a decoder of `B` on the *remaining* bytes after applying this decoder, then returns a pair of the individual values `(a, b)`.
    ///
    /// This enables the application of decoders in sequence where a step does not depend on its predecessor (when such a dependency exists, consider [`DecoderExt::and_then`].
    ///
    /// The next decoder can return an error type `EE` other than `E` as long as there is an implicit conversion [`From<E>`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use tokio_util::codec::Decoder;
    /// # use bytes::BytesMut;
    /// use tokio_util_codec_compose::{combinators::DecoderExt, elements::uint8};
    ///
    /// let pair = uint8().then(uint8()).decode(&mut BytesMut::from("\x2A\x3B")).unwrap();
    ///
    /// assert_eq!(pair, Some((0x2A, 0x3B)));
    /// ```
    // TODO: Flatten resulting tuple.
    fn then<DNext, B, EE>(self, next: DNext) -> DecoderThen<Self, DNext, A, EE>
    where
        DNext: Decoder<Item = B, Error = EE>,
        EE: From<E>,
        Self: Sized,
    {
        DecoderThen {
            first: self,
            second: next,
            first_value: None,
            _error: PhantomData,
        }
    }

    /// Chains a function `f` of type `&A -> Box<Decoder<Item = B, Error = E>>` over the decoded value when that is `Ok(Some(a))`.
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
    /// Notice that `f` can't take ownership of the first value `a`, hence the shared borrow, because otherwise it would not be possible to decode incomplete frames
    /// without cloning or maybe saving incoming bytes and re-running this decoder. If you need access to the first value, use [`DecoderAndThen::first_value`]
    /// or [`DecoderAndThen::first_value_as_mut`].
    ///
    /// # Stateful decoders and multi-frames
    ///
    /// Due to the stateful behaviour of this combinator, if you need to decode multiple frames, you'd need to [`DecoderAndThen::reset`] between frames to clean up
    /// the previous value `a` and therefore its influence on `b`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tokio_util::codec::Decoder;
    /// # use bytes::BytesMut;
    /// use tokio_util_codec_compose::{combinators::{decode::DecoderBoxed, DecoderExt}, elements::{uint8, uint16_be, uint16_le}};
    ///
    /// fn payload_for_version(version: &u8) -> DecoderBoxed<u16, std::io::Error> {
    ///     if *version == 0x01 { uint16_be().boxed() } else { uint16_le().boxed() }
    /// }
    ///
    /// let mut decoder = uint8().and_then(payload_for_version);
    ///
    /// let device_big_endian = decoder.decode(&mut BytesMut::from("\x01\x2A\x3B")).unwrap();
    /// assert_eq!(device_big_endian, Some(0x2A3B));
    ///
    /// decoder.reset();
    ///
    /// let device_little_endian = decoder.decode(&mut BytesMut::from("\x00\x2A\x3B")).unwrap();
    /// assert_eq!(device_little_endian, Some(0x3B2A));
    /// ```
    fn and_then<F, DNext, B, EE>(self, f: F) -> DecoderAndThen<Self, F, DNext, A, EE>
    where
        F: Fn(&A) -> DNext,
        DNext: Decoder<Item = B, Error = EE>,
        EE: From<E>,
        Self: Sized,
    {
        DecoderAndThen {
            first: self,
            to_second: f,
            _second: PhantomData,
            first_value: None,
            _error: PhantomData,
        }
    }

    /// Shorthand for boxing this decoder while also widening its type to ease inference and spelling.
    ///
    /// That's probably useful when combined with [`DecoderExt::and_then`] where the continuation
    /// yields decoders with different types.
    fn boxed(self) -> DecoderBoxed<A, E>
    where
        Self: Sized,
        Self: 'static,
    {
        DecoderBoxed {
            inner: Box::new(self),
        }
    }
}

impl<D, A, E> DecoderExt<A, E> for D where D: Decoder<Item = A, Error = E> {}

/// A decoder for applying a non-fallible transformation on the success type.
///
/// The result of [`Decoder::map`].
#[must_use = "decoders do nothing unless used"]
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

/// A decoder for applying a non-fallible conversion onto the success type.
///
/// The result of [`Decoder::map_into`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderMapInto<D, B> {
    inner: D,
    _target: PhantomData<B>,
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

/// A decoder for applying a fallible transformation on the success type.
///
/// The result of [`Decoder::try_map`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderTryMap<D, F, E> {
    inner: D,
    f: F,
    _error: PhantomData<E>,
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

/// A decoder for applying a fallible conversion onto the success type.
///
/// The result of [`Decoder::try_map_into`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderTryMapInto<D, B, E> {
    inner: D,
    _target: PhantomData<B>,
    _error: PhantomData<E>,
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

/// A decoder for applying a fallible transformation on the error type.
///
/// The result of [`Decoder::map_err`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderMapErr<D, F> {
    inner: D,
    f: F,
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

/// A decoder for sequence decoders with no interdependency between each other.
///
/// The result of [`Decoder::then`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderThen<DFirst, DSecond, A, E> {
    first: DFirst,
    second: DSecond,
    first_value: Option<A>,
    _error: PhantomData<E>,
}

impl<DFirst, DSecond, A, B, EA, EB, EE> Decoder for DecoderThen<DFirst, DSecond, A, EE>
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
        if self.first_value.is_none() {
            self.first_value = self.first.decode(src)?;
        }

        let second_value = if self.first_value.is_none() {
            None
        } else {
            self.second.decode(src)?
        };

        match (&mut self.first_value, second_value) {
            both @ (Some(_), Some(_)) => Ok(both.0.take().zip(both.1)),
            _ => Ok(None),
        }
    }
}

/// A decoder for sequence decoders with interdependency between each other.
///
/// The result of [`Decoder::and_then`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderAndThen<DFirst, F, DSecond, A, E> {
    first: DFirst,
    to_second: F,
    _second: PhantomData<DSecond>,
    first_value: Option<A>,
    _error: PhantomData<E>,
}

impl<DFirst, F, DSecond, A, EE> DecoderAndThen<DFirst, F, DSecond, A, EE> {
    /// Accesses the first decoder value.
    pub fn first_value(&self) -> Option<&A> {
        self.first_value.as_ref()
    }

    /// Mutably accesses the first decoder value.
    pub fn first_value_as_mut(&mut self) -> Option<&mut A> {
        self.first_value.as_mut()
    }

    /// Resets the state of this decoder for decoding subsequent frames.
    pub fn reset(&mut self) {
        self.first_value = None;
    }
}

impl<DFirst, F, DSecond, A, B, EA, EB, EE> Decoder for DecoderAndThen<DFirst, F, DSecond, A, EE>
where
    DFirst: Decoder<Item = A, Error = EA>,
    F: Fn(&A) -> DSecond,
    DSecond: Decoder<Item = B, Error = EB>,
    EA: From<io::Error>,
    EB: From<io::Error>,
    EE: From<io::Error> + From<EA> + From<EB>,
{
    type Item = B;

    type Error = EE;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        if self.first_value.is_none() {
            self.first_value = self.first.decode(src)?;
        }

        Ok(self
            .first_value
            .as_ref()
            .and_then(|v| (self.to_second)(v).decode(src).transpose())
            .transpose()?)
    }
}

/// A decoder that boxes another decoder.
///
/// The result of [`Decoder::boxed`].
#[must_use = "decoders do nothing unless used"]
pub struct DecoderBoxed<A, E> {
    inner: Box<dyn Decoder<Item = A, Error = E>>,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elements::{uint16_be, uint16_le, uint8};
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
        #[derive(Debug, PartialEq, Eq)]
        struct Device(u8);
        let mut decoder = uint8().map(Device);

        let mut src = BytesMut::from("\x01");
        let value = decoder.decode(&mut src)?;

        assert!(matches!(value, Some(Device(0x01))));
        assert_eq!(src, BytesMut::default());

        Ok(())
    }

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

    #[test]
    fn decode_try_map_into_succeed() {
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

        let mut decoder = uint8().try_map_into::<Version>();

        let mut src = BytesMut::from("\x01");
        let ok = decoder.decode(&mut src);

        assert!(matches!(ok, Ok(Some(Version::V1))));
        assert_eq!(src, BytesMut::default());
    }

    #[test]
    fn decode_try_map_into_fail() {
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

        let mut decoder = uint8().try_map_into::<Version>();

        let mut src = BytesMut::from("\x02");
        let err = decoder.decode(&mut src);
        let err_kind = err.map_err(|e| e.kind());

        assert!(matches!(err_kind, Err(io::ErrorKind::InvalidData)));
        assert_eq!(src, BytesMut::default());
    }

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

    #[test]
    fn decode_then_single_pass() -> anyhow::Result<()> {
        let mut decoder = uint16_be().then(uint8());

        let mut src = BytesMut::from("\x01\x02\x03");
        let value = decoder.decode(&mut src)?;

        assert_eq!(value, Some((0x0102, 0x03)));
        assert_eq!(src, BytesMut::default());

        Ok(())
    }

    #[test]
    fn decode_then_multi_pass_with_first_decoder_full() -> anyhow::Result<()> {
        let mut decoder = uint16_be().then(uint8());

        let mut src = BytesMut::from("\x01\x02");
        let value = decoder.decode(&mut src)?;

        assert_eq!(value, None);
        assert_eq!(src, BytesMut::default());

        let mut src = BytesMut::from("\x03");
        let value = decoder.decode(&mut src)?;

        assert_eq!(value, Some((0x0102, 0x03)));
        assert_eq!(src, BytesMut::default());

        Ok(())
    }

    #[test]
    fn decode_then_multi_pass_with_first_decoder_waiting_for_bytes() -> anyhow::Result<()> {
        let mut decoder = uint16_be().then(uint8());

        let mut src = BytesMut::from("\x01");
        let value = decoder.decode(&mut src)?;

        assert_eq!(value, None);
        assert_eq!(src, BytesMut::from("\x01"));

        let mut src = BytesMut::from("\x01\x02\x03");
        let value = decoder.decode(&mut src)?;

        assert_eq!(value, Some((0x0102, 0x03)));
        assert_eq!(src, BytesMut::default());

        Ok(())
    }

    #[test]
    fn decode_and_then_with_dependency_on_previous_value() -> anyhow::Result<()> {
        let mut decoder = uint8().and_then(|version| {
            if *version == 0x01 {
                uint16_be().boxed()
            } else {
                uint16_le().boxed()
            }
        });

        let mut src = BytesMut::from("\x01\x02\x03");
        let value = decoder.decode(&mut src)?;

        assert_eq!(value, Some(0x0203));
        assert_eq!(decoder.first_value(), Some(&0x01));
        assert_eq!(decoder.first_value_as_mut(), Some(&mut 0x01));
        assert_eq!(src, BytesMut::default());

        decoder.reset();

        let mut src = BytesMut::from("\x02\x02\x03");
        let value = decoder.decode(&mut src)?;

        assert_eq!(value, Some(0x0302));
        assert_eq!(decoder.first_value(), Some(&0x02));
        assert_eq!(decoder.first_value_as_mut(), Some(&mut 0x02));
        assert_eq!(src, BytesMut::default());

        Ok(())
    }

    #[test]
    fn decode_and_then_single_pass() -> anyhow::Result<()> {
        let mut decoder = uint16_be().and_then(|_| uint8());

        let mut src = BytesMut::from("\x01\x02\x03");
        let value = decoder.decode(&mut src)?;

        assert_eq!(value, Some(0x03));
        assert_eq!(decoder.first_value(), Some(&0x0102));
        assert_eq!(decoder.first_value_as_mut(), Some(&mut 0x0102));
        assert_eq!(src, BytesMut::default());

        Ok(())
    }

    #[test]
    fn decode_and_then_multi_pass_with_first_decoder_full() -> anyhow::Result<()> {
        let mut decoder = uint16_be().and_then(|_| uint8());

        let mut src = BytesMut::from("\x01\x02");
        let value = decoder.decode(&mut src)?;

        assert_eq!(value, None);
        assert_eq!(src, BytesMut::default());

        let mut src = BytesMut::from("\x03");
        let value = decoder.decode(&mut src)?;

        assert_eq!(value, Some(0x03));
        assert_eq!(decoder.first_value(), Some(&0x0102));
        assert_eq!(decoder.first_value_as_mut(), Some(&mut 0x0102));
        assert_eq!(src, BytesMut::default());

        Ok(())
    }

    #[test]
    fn decode_and_then_multi_pass_with_first_decoder_waiting_for_bytes() -> anyhow::Result<()> {
        let mut decoder = uint16_be().and_then(|_| uint8());

        let mut src = BytesMut::from("\x01");
        let value = decoder.decode(&mut src)?;

        assert_eq!(value, None);
        assert_eq!(src, BytesMut::from("\x01"));

        let mut src = BytesMut::from("\x01\x02\x03");
        let value = decoder.decode(&mut src)?;

        assert_eq!(value, Some(0x03));
        assert_eq!(decoder.first_value(), Some(&0x0102));
        assert_eq!(decoder.first_value_as_mut(), Some(&mut 0x0102));
        assert_eq!(src, BytesMut::default());

        Ok(())
    }

    #[test]
    fn decode_and_then_first_fail() {
        let mut decoder = DecoderFail::default().and_then(|_| uint8());

        let mut src = BytesMut::from("\x01\x02\x03");
        let err = decoder.decode(&mut src);

        let err_kind = err.map_err(|e| e.kind());

        assert!(matches!(err_kind, Err(io::ErrorKind::Other)));
        assert_eq!(src, BytesMut::from("\x01\x02\x03"));
    }

    #[test]
    fn decode_and_then_second_fail() {
        let mut decoder = uint8().and_then(|_| DecoderFail::default());

        let mut src = BytesMut::from("\x01\x02\x03");
        let err = decoder.decode(&mut src);

        let err_kind = err.map_err(|e| e.kind());

        assert!(matches!(err_kind, Err(io::ErrorKind::Other)));
        assert_eq!(src, BytesMut::from("\x02\x03"));
    }

    #[derive(Debug, Default)]
    struct DecoderFail;
    impl Decoder for DecoderFail {
        type Item = u16;

        type Error = io::Error;

        fn decode(&mut self, _src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
            Err(io::ErrorKind::Other.into())
        }
    }
}
