//! A set of compositional operations on [`tokio_util::codec::Encoder`].

pub mod combinators;

pub use self::combinators::EncoderExt;
