//! A set of adaptors implementing compositional operations for decoding.

mod and_then;
mod boxed;
mod map;
mod map_err;
mod map_into;
mod then;
mod try_map;
mod try_map_into;

pub use self::{
    and_then::DecoderAndThen, boxed::DecoderBoxed, map::DecoderMap, map_err::DecoderMapErr,
    map_into::DecoderMapInto, then::DecoderThen, try_map::DecoderTryMap,
    try_map_into::DecoderTryMapInto,
};
