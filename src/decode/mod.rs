//! A set of structures and compositional operations on [`Decoder`].
//!
//! The operations take simpler decoders as inputs with customization functions and produce more powerful ones as output.

pub mod adaptors;

use self::adaptors::{
    DecoderAndThen, DecoderBoxed, DecoderMap, DecoderMapErr, DecoderMapInto, DecoderThen,
    DecoderTryMap, DecoderTryMapInto,
};

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
    /// use tokio_util_codec_compose::{decode::DecoderExt, primitives::uint8};
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
        DecoderMap::new(self, f)
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
    /// use tokio_util_codec_compose::{decode::DecoderExt, primitives::uint8};
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
        DecoderMapInto::new(self)
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
    /// use tokio_util_codec_compose::{decode::DecoderExt, primitives::uint8};
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
        DecoderTryMap::new(self, f)
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
    /// use tokio_util_codec_compose::{decode::DecoderExt, primitives::uint8};
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
        DecoderTryMapInto::new(self)
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
    /// use tokio_util_codec_compose::{decode::DecoderExt, primitives::uint8};
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
        DecoderMapErr::new(self, f)
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
    /// use tokio_util_codec_compose::{decode::DecoderExt, primitives::uint8};
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
        DecoderThen::new(self, next)
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
    /// use tokio_util_codec_compose::{decode::{adaptors::DecoderBoxed, DecoderExt}, primitives::{uint8, uint16_be, uint16_le}};
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
        DecoderAndThen::new(self, f)
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
        DecoderBoxed::new(self)
    }
}

impl<D, A, E> DecoderExt<A, E> for D where D: Decoder<Item = A, Error = E> {}
