//! Building blocks for composing codecs.

pub mod ints;

/// Shorthand notation to construct an [`ints::U8`].
pub fn uint8() -> ints::U8 {
    ints::U8::default()
}

/// Shorthand notation to construct an [`ints::U16LE`].
pub fn uint16_le() -> ints::U16LE {
    ints::U16LE::default()
}

/// Shorthand notation to construct an [`ints::U16BE`].
pub fn uint16_be() -> ints::U16BE {
    ints::U16BE::default()
}

/// Shorthand notation to construct an [`ints::U32LE`].
pub fn uint32_le() -> ints::U32LE {
    ints::U32LE::default()
}

/// Shorthand notation to construct an [`ints::U32BE`].
pub fn uint32_be() -> ints::U32BE {
    ints::U32BE::default()
}
