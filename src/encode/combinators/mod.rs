//! A set compositional operations on [`Encoder`].
//!
//! The operations take simpler encoders as inputs with customization functions and produce more powerful ones as output.

pub mod adaptors;

use self::adaptors::EncoderContraMap;

use tokio_util::codec::Encoder;

/// Extension of [`Encoder`] with compositional operations.
pub trait EncoderExt<A, E>: Encoder<A, Error = E> {
    /// Applies a function `f` of type `B -> A` over the input before encoding.
    ///
    /// So, if you have a value of type `A` for which there's an `Encoder<A>`, and you have a function `B -> A`,
    /// then you can obtain an `Encoder<B>`. Notice that the arrows are "reversed" if compared
    /// against a typical `map` operation.
    ///
    /// The function `f` cannot fail.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tokio_util::codec::Decoder;
    /// # use bytes::BytesMut;
    /// use tokio_util_codec_compose::{decode::{combinators::DecoderExt, primitives::uint8}};
    ///
    /// # #[derive(Debug, PartialEq, Eq)]
    /// struct Device(u8);
    ///
    /// let device = uint8().map(Device).decode(&mut BytesMut::from("\x2A")).unwrap();
    /// assert_eq!(device, Some(Device(42)));
    /// ```
    fn contra_map<F, B>(self, f: F) -> EncoderContraMap<Self, F>
    where
        F: Fn(B) -> A,
        Self: Sized,
    {
        EncoderContraMap::new(self, f)
    }
}

impl<C, A, E> EncoderExt<A, E> for C where C: Encoder<A, Error = E> {}
