//! Runtime encoding registry for CLI tools.
//!
//! This module provides a way to discover and use encodings at runtime,
//! useful for tools like `iconv` that need to select encodings by name.
//!
//! # Example
//!
//! ```ignore
//! use stringly::registry;
//!
//! // List available encodings
//! for enc in registry::encodings() {
//!     println!("{}", enc.name());
//! }
//!
//! // Transcode between encodings
//! let output = registry::transcode(input_bytes, "UTF-8", "ISO-8859-1")?;
//! ```

use alloc::string::ToString;
use alloc::vec::Vec;

use crate::error::EncodingError;

/// Error returned when an encoding is not found.
#[derive(Debug, Clone)]
pub struct UnknownEncodingError(pub alloc::string::String);

impl core::fmt::Display for UnknownEncodingError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "unknown encoding: {}", self.0)
    }
}

impl core::error::Error for UnknownEncodingError {}

/// Error returned during transcoding.
#[derive(Debug)]
pub enum TranscodeError {
    /// The source encoding is unknown.
    UnknownSourceEncoding(UnknownEncodingError),
    /// The target encoding is unknown.
    UnknownTargetEncoding(UnknownEncodingError),
    /// The input bytes are not valid for the source encoding.
    InvalidInput(EncodingError),
    /// A character cannot be represented in the target encoding.
    UnencodableChar(char),
}

impl core::fmt::Display for TranscodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnknownSourceEncoding(e) => write!(f, "source {}", e),
            Self::UnknownTargetEncoding(e) => write!(f, "target {}", e),
            Self::InvalidInput(e) => write!(f, "invalid input: {}", e),
            Self::UnencodableChar(c) => write!(f, "cannot encode character: {:?}", c),
        }
    }
}

impl core::error::Error for TranscodeError {}

/// A registered encoding entry.
///
/// Each encoding registers one of these via `inventory::submit!`.
pub struct EncodingEntry {
    /// The canonical name of the encoding (e.g., "UTF-8").
    pub name: &'static str,
    /// Alternative names for the encoding (e.g., &["UTF8"]).
    pub aliases: &'static [&'static str],
    /// Whether this encoding can represent all Unicode code points.
    pub is_unicode: bool,
    /// Decode bytes to a sequence of chars.
    pub decode: fn(&[u8]) -> Result<Vec<char>, EncodingError>,
    /// Encode a char, returning the bytes. Returns None if unencodable.
    pub try_encode_char: fn(char) -> Option<Vec<u8>>,
}

impl EncodingEntry {
    /// Returns the canonical name of this encoding.
    pub fn name(&self) -> &'static str {
        self.name
    }

    /// Returns whether this encoding can represent all Unicode code points.
    pub fn is_unicode(&self) -> bool {
        self.is_unicode
    }

    /// Returns all names (canonical + aliases) for this encoding.
    pub fn all_names(&self) -> impl Iterator<Item = &'static str> {
        core::iter::once(self.name).chain(self.aliases.iter().copied())
    }

    /// Check if this encoding matches the given name (case-insensitive).
    pub fn matches(&self, name: &str) -> bool {
        self.all_names().any(|n| n.eq_ignore_ascii_case(name))
    }
}

inventory::collect!(EncodingEntry);

/// Returns an iterator over all registered encodings.
pub fn encodings() -> impl Iterator<Item = &'static EncodingEntry> {
    inventory::iter::<EncodingEntry>()
}

/// Find an encoding by name (case-insensitive).
pub fn find_encoding(name: &str) -> Result<&'static EncodingEntry, UnknownEncodingError> {
    encodings()
        .find(|e| e.matches(name))
        .ok_or_else(|| UnknownEncodingError(name.to_string()))
}

/// Transcode bytes from one encoding to another.
///
/// # Arguments
///
/// * `input` - The input bytes in the source encoding
/// * `from` - The name of the source encoding
/// * `to` - The name of the target encoding
///
/// # Returns
///
/// The transcoded bytes in the target encoding, or an error.
pub fn transcode(input: &[u8], from: &str, to: &str) -> Result<Vec<u8>, TranscodeError> {
    let from_enc = find_encoding(from).map_err(TranscodeError::UnknownSourceEncoding)?;
    let to_enc = find_encoding(to).map_err(TranscodeError::UnknownTargetEncoding)?;

    // Decode input to chars
    let chars = (from_enc.decode)(input).map_err(TranscodeError::InvalidInput)?;

    // Encode chars to output
    let mut output = Vec::new();
    for c in chars {
        match (to_enc.try_encode_char)(c) {
            Some(bytes) => output.extend(bytes),
            None => return Err(TranscodeError::UnencodableChar(c)),
        }
    }

    Ok(output)
}
