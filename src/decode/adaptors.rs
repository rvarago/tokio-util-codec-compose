//! A set of adaptors implementing compositional operations for decodingx.

// TODO: Split structs into modules (once per file?).

use bytes::BytesMut;
use std::{io, marker::PhantomData};
use tokio_util::codec::Decoder;

/// A decoder for applying a non-fallible transformation on the success type.
///
/// The result of [`super::DecoderExt::map`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderMap<D, F> {
    inner: D,
    f: F,
}

impl<D, F> DecoderMap<D, F> {
    pub(super) fn new(inner: D, f: F) -> Self {
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

/// A decoder for applying a non-fallible conversion onto the success type.
///
/// The result of [`super::DecoderExt::map_into`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderMapInto<D, B> {
    inner: D,
    _target: PhantomData<B>,
}

impl<D, B> DecoderMapInto<D, B> {
    pub(super) fn new(inner: D) -> Self {
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

/// A decoder for applying a fallible transformation on the success type.
///
/// The result of [`super::DecoderExt::try_map`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderTryMap<D, F, E> {
    inner: D,
    f: F,
    _error: PhantomData<E>,
}

impl<D, F, E> DecoderTryMap<D, F, E> {
    pub(super) fn new(inner: D, f: F) -> Self {
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

/// A decoder for applying a fallible conversion onto the success type.
///
/// The result of [`super::DecoderExt::try_map_into`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderTryMapInto<D, B, E> {
    inner: D,
    _target: PhantomData<B>,
    _error: PhantomData<E>,
}

impl<D, B, E> DecoderTryMapInto<D, B, E> {
    pub(super) fn new(inner: D) -> Self {
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

/// A decoder for applying a fallible transformation on the error type.
///
/// The result of [`super::DecoderExt::map_err`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderMapErr<D, F> {
    inner: D,
    f: F,
}

impl<D, F> DecoderMapErr<D, F> {
    pub(super) fn new(inner: D, f: F) -> Self {
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

/// A decoder for sequence decoders with no interdependency between each other.
///
/// The result of [`super::DecoderExt::then`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderThen<DFirst, DSecond, A, E> {
    first: DFirst,
    second: DSecond,
    first_value: Option<A>,
    _error: PhantomData<E>,
}

impl<DFirst, DSecond, A, E> DecoderThen<DFirst, DSecond, A, E> {
    pub(super) fn new(first: DFirst, second: DSecond) -> Self {
        Self {
            first,
            second,
            first_value: None,
            _error: PhantomData,
        }
    }
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
/// The result of [`super::DecoderExt::and_then`].
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
    pub(super) fn new(first: DFirst, to_second: F) -> Self {
        Self {
            first,
            to_second,
            _second: PhantomData,
            first_value: None,
            _error: PhantomData,
        }
    }

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
/// The result of [`super::DecoderExt::boxed`].
#[must_use = "decoders do nothing unless used"]
pub struct DecoderBoxed<A, E> {
    inner: Box<dyn Decoder<Item = A, Error = E>>,
}

impl<A, E> DecoderBoxed<A, E> {
    pub(super) fn new<D>(inner: D) -> Self
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

#[cfg(test)]
mod tests {
    use super::*;

    use super::super::DecoderExt;
    use crate::primitives::{uint16_be, uint16_le, uint8};
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
    fn decode_then_decoding_two_complete_frames() -> anyhow::Result<()> {
        let mut decoder = uint8().then(uint8());

        let mut src = BytesMut::from("\x01\x02");
        let value = decoder.decode(&mut src)?;

        assert_eq!(value, Some((0x01, 0x02)));
        assert_eq!(src, BytesMut::default());

        let mut src = BytesMut::from("\x02\x03");
        let value = decoder.decode(&mut src)?;

        assert_eq!(value, Some((0x02, 0x03)));
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
