//! An adaptor for chaining decoders with no interdependencies.

use bytes::BytesMut;
use std::{io, marker::PhantomData};
use tokio_util::codec::Decoder;

/// A decoder for sequence decoders with interdependency between each other.
///
/// The result of [`crate::decode::DecoderExt::and_then`].
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
    pub(in crate::decode) fn new(first: DFirst, to_second: F) -> Self {
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

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{
        decode::DecoderExt,
        primitives::{uint16_be, uint16_le, uint8},
    };

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
