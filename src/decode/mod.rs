//! A set of compositional operations on [`tokio_util::codec::Decoder`].
//!
//! The operations take simpler decoders as inputs with customization functions and produce more powerful ones as output.

pub mod combinators;

pub use self::combinators::DecoderExt;
