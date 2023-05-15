//! An adaptor for chaining decoders with no interdependencies.

use bytes::BytesMut;
use std::{io, marker::PhantomData};
use tokio_util::codec::Decoder;

/// A decoder for sequence decoders with no interdependency between each other.
///
/// The result of [`crate::decode::combinators::DecoderExt::then`].
#[must_use = "decoders do nothing unless used"]
#[derive(Debug)]
pub struct DecoderThen<DFirst, DSecond, A, E> {
    first: DFirst,
    second: DSecond,
    first_value: Option<A>,
    _error: PhantomData<E>,
}

impl<DFirst, DSecond, A, E> DecoderThen<DFirst, DSecond, A, E> {
    pub(in crate::decode::combinators) fn new(first: DFirst, second: DSecond) -> Self {
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

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{
        decode::combinators::DecoderExt,
        primitives::{uint16_be, uint8},
    };

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
}
