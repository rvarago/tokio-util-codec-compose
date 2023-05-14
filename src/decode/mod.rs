//! A set of structures and compositional operations on [`tokio_util::codec::Decoder`].
//!
//! The operations take simpler decoders as inputs with customization functions and produce more powerful ones as output.

pub mod combinators;
pub mod primitives;

pub use combinators::DecoderExt;
