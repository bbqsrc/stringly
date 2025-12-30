//! Encoding traits for character encoding implementations.
//!
//! This module provides the core traits that define how characters are encoded:
//!
//! - [`Encoding`]: Base trait for all encodings
//! - [`LimitedEncoding`]: Marker for encodings that cannot represent all Unicode
//! - [`UniversalEncoding`]: Marker for encodings that can represent all Unicode
//!
//! # Example
//!
//! ```
//! use stringly::{Encoding, Utf8};
//!
//! // Check encoding properties
//! assert_eq!(Utf8::NAME, "UTF-8");
//! assert!(!Utf8::IS_FIXED_WIDTH);
//! assert_eq!(Utf8::MAX_CHAR_LEN, 4);
//!
//! // Validate bytes
//! assert!(Utf8::validate(b"hello").is_ok());
//! assert!(Utf8::validate(b"\xff\xfe").is_err());
//!
//! // Encode a character
//! let mut buf = [0u8; 4];
//! let len = Utf8::encode_char('a', &mut buf);
//! assert_eq!(&buf[..len], b"a");
//!
//! let len = Utf8::encode_char('\u{1F600}', &mut buf);
//! assert_eq!(len, 4); // Emoji takes 4 bytes in UTF-8
//! ```

use crate::error::EncodingError;

/// A trait defining a character encoding.
///
/// Implementors are zero-sized types (ZSTs) that serve as type-level markers
/// for the encoding of a string. All encoding operations are static methods.
pub trait Encoding: Sized + 'static {
    /// The human-readable name of this encoding (e.g., "UTF-8", "UTF-16LE").
    const NAME: &'static str;

    /// Whether this encoding uses a fixed number of bytes per character.
    const IS_FIXED_WIDTH: bool;

    /// The number of bytes per character, if this is a fixed-width encoding.
    /// Returns `None` for variable-width encodings.
    const BYTES_PER_CHAR: Option<usize>;

    /// The maximum number of bytes a single character can occupy in this encoding.
    const MAX_CHAR_LEN: usize;

    /// The number of bytes used to represent the null character ('\0') in this encoding.
    ///
    /// For UTF-8 and single-byte encodings this is 1.
    /// For UTF-16 this is 2 (the code unit 0x0000).
    /// For UTF-32 this is 4 (the code unit 0x00000000).
    const NULL_LEN: usize = 1;

    /// Validates that the given byte slice is valid for this encoding.
    ///
    /// Returns `Ok(())` if the bytes are valid, or an `EncodingError` indicating
    /// where validation failed.
    fn validate(bytes: &[u8]) -> Result<(), EncodingError>;

    /// Decodes a character starting at the given byte offset.
    ///
    /// Returns `Some((char, next_offset))` where `next_offset` is the byte index
    /// immediately after the decoded character, or `None` if no valid character
    /// starts at `offset`.
    ///
    /// # Panics
    ///
    /// May panic if `offset` is out of bounds or not on a character boundary.
    fn decode_char_at(bytes: &[u8], offset: usize) -> Option<(char, usize)>;

    /// Returns the number of bytes needed to encode the given character.
    fn encoded_len(c: char) -> usize;

    /// Encodes a character into the given buffer.
    ///
    /// Returns the number of bytes written.
    ///
    /// # Panics
    ///
    /// Panics if the buffer is too small to hold the encoded character.
    fn encode_char(c: char, buf: &mut [u8]) -> usize;

    /// Checks if the given index is a valid character boundary in the byte slice.
    ///
    /// For self-synchronizing encodings like UTF-8, this is O(1).
    /// For non-self-synchronizing encodings, this may be O(n).
    fn is_char_boundary(bytes: &[u8], index: usize) -> bool;

    /// Decodes the character ending just before the given byte offset.
    ///
    /// Returns `Some((char, start_offset))` where `start_offset` is the byte index
    /// where the character starts, or `None` if no valid character ends at `offset`.
    ///
    /// For non-self-synchronizing encodings, this may be O(n) as it needs to scan
    /// from the beginning to find character boundaries.
    fn decode_char_before(bytes: &[u8], offset: usize) -> Option<(char, usize)>;

    /// Attempts to encode a character into the given buffer.
    ///
    /// Returns `Some(bytes_written)` if the character can be represented in this
    /// encoding, or `None` if the character cannot be encoded.
    ///
    /// For encodings that can represent all Unicode characters (UTF-8, UTF-16, UTF-32),
    /// this always returns `Some`. For limited encodings like codepages, this returns
    /// `None` for characters outside the encoding's repertoire.
    ///
    /// # Panics
    ///
    /// Panics if the buffer is too small to hold the encoded character.
    fn try_encode_char(c: char, buf: &mut [u8]) -> Option<usize> {
        Some(Self::encode_char(c, buf))
    }

    /// Returns `true` if this encoding can represent the given character.
    ///
    /// For encodings that can represent all Unicode characters (UTF-8, UTF-16, UTF-32),
    /// this always returns `true`. For limited encodings like codepages, this returns
    /// `false` for characters outside the encoding's repertoire.
    fn can_encode(c: char) -> bool {
        let _ = c;
        true
    }
}

/// Marker trait for encodings that cannot represent all Unicode code points.
///
/// Encodings implementing this trait may fail to encode certain Unicode characters.
/// Use `TryFrom` for conversions to these encodings.
pub trait LimitedEncoding: Encoding {}

/// Marker trait for encodings that can represent all Unicode code points.
///
/// These encodings (UTF-8, UTF-16, UTF-32, GB18030) can losslessly encode any
/// Unicode character, making conversions between them infallible.
pub trait UniversalEncoding: Encoding {}
