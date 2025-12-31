//! UTF-7 encoding implementations.
//!
//! This module provides two UTF-7 variants:
//!
//! - [`Utf7`]: Standard UTF-7 per RFC 2152
//! - [`Utf7Imap`]: Modified UTF-7 for IMAP mailbox names per RFC 3501
//!
//! # UTF-7 Overview
//!
//! UTF-7 is a 7-bit safe encoding for Unicode text. It encodes non-ASCII characters
//! using a modified Base64 encoding prefixed by `+` and terminated by `-` or any
//! direct character.
//!
//! # Standard UTF-7 (RFC 2152)
//!
//! - Direct characters pass through unchanged: A-Z, a-z, 0-9, and `'(),-./:?`
//! - `+` starts a Base64-encoded sequence of UTF-16BE code units
//! - `-` terminates a Base64 sequence (or any direct character implicitly terminates it)
//! - `+-` encodes a literal `+`
//!
//! # Modified UTF-7 for IMAP (RFC 3501)
//!
//! - Uses `&` instead of `+` for shifting
//! - `&-` encodes a literal `&`
//! - Uses `,` instead of `/` in the Base64 alphabet
//! - Used for IMAP mailbox names

use alloc::vec::Vec;

use crate::encoding::{Encoding, UniversalEncoding};
use crate::error::EncodingError;

// Standard Base64 alphabet (RFC 2152)
const BASE64_STD: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

// Modified Base64 alphabet for IMAP (RFC 3501) - uses ',' instead of '/'
const BASE64_IMAP: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+,";

/// Standard UTF-7 encoding per RFC 2152.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Utf7;

/// Modified UTF-7 encoding for IMAP mailbox names per RFC 3501.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Utf7Imap;

/// Decoder state for UTF-7.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    /// Direct mode - ASCII characters pass through
    Direct,
    /// Base64 mode - decoding UTF-16BE encoded in Base64
    Base64,
}

/// Configuration for UTF-7 variants.
trait Utf7Config {
    /// The shift character ('+' for standard, '&' for IMAP)
    const SHIFT_CHAR: u8;
    /// The Base64 alphabet to use
    const BASE64_ALPHABET: &'static [u8; 64];
}

impl Utf7Config for Utf7 {
    const SHIFT_CHAR: u8 = b'+';
    const BASE64_ALPHABET: &'static [u8; 64] = BASE64_STD;
}

impl Utf7Config for Utf7Imap {
    const SHIFT_CHAR: u8 = b'&';
    const BASE64_ALPHABET: &'static [u8; 64] = BASE64_IMAP;
}

/// Returns true if the character is a direct (passthrough) character in standard UTF-7.
/// Set D (directly encoded): A-Z, a-z, 0-9, ' ( ) , - . / : ?
/// Plus space, tab, CR, LF
#[inline]
fn is_direct_std(b: u8) -> bool {
    matches!(b,
        b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' |
        b'\'' | b'(' | b')' | b',' | b'-' | b'.' | b'/' | b':' | b'?' |
        b' ' | b'\t' | b'\r' | b'\n'
    )
}

/// Returns true if the character is a direct character in IMAP UTF-7.
/// All printable ASCII except '&' (0x20-0x25, 0x27-0x7E)
#[inline]
fn is_direct_imap(b: u8) -> bool {
    (0x20..=0x7E).contains(&b) && b != b'&'
}

/// Decode a Base64 character to its 6-bit value.
fn base64_decode(b: u8, alphabet: &[u8; 64]) -> Option<u8> {
    alphabet.iter().position(|&c| c == b).map(|p| p as u8)
}

/// Core UTF-7 implementation that works for both variants.
fn validate_utf7<C: Utf7Config>(bytes: &[u8]) -> Result<(), EncodingError> {
    let mut i = 0;
    let is_direct = if C::SHIFT_CHAR == b'+' {
        is_direct_std
    } else {
        is_direct_imap
    };

    while i < bytes.len() {
        let b = bytes[i];

        if b == C::SHIFT_CHAR {
            // Start of shifted sequence
            i += 1;
            if i >= bytes.len() {
                return Err(EncodingError::new(i - 1, Some(1)));
            }

            // Check for shift-char followed by '-' (literal shift char)
            if bytes[i] == b'-' {
                i += 1;
                continue;
            }

            // Decode Base64 sequence
            let mut base64_bits: u32 = 0;
            let mut bit_count = 0;
            let mut utf16_buf: Vec<u16> = Vec::new();

            while i < bytes.len() {
                let b = bytes[i];

                if b == b'-' {
                    // Explicit end of Base64 sequence
                    i += 1;
                    break;
                }

                if let Some(val) = base64_decode(b, C::BASE64_ALPHABET) {
                    base64_bits = (base64_bits << 6) | val as u32;
                    bit_count += 6;

                    // Extract 16-bit code units
                    while bit_count >= 16 {
                        bit_count -= 16;
                        let code_unit = ((base64_bits >> bit_count) & 0xFFFF) as u16;
                        utf16_buf.push(code_unit);
                    }
                    i += 1;
                } else if is_direct(b) {
                    // Implicit end - direct character terminates Base64
                    break;
                } else {
                    return Err(EncodingError::new(i, Some(1)));
                }
            }

            // Validate UTF-16 surrogate pairs
            let mut j = 0;
            while j < utf16_buf.len() {
                let cu = utf16_buf[j];
                if (0xD800..=0xDBFF).contains(&cu) {
                    // High surrogate - must be followed by low surrogate
                    if j + 1 >= utf16_buf.len() {
                        return Err(EncodingError::new(i, None));
                    }
                    let cu2 = utf16_buf[j + 1];
                    if !(0xDC00..=0xDFFF).contains(&cu2) {
                        return Err(EncodingError::new(i, None));
                    }
                    j += 2;
                } else if (0xDC00..=0xDFFF).contains(&cu) {
                    // Lone low surrogate
                    return Err(EncodingError::new(i, None));
                } else {
                    j += 1;
                }
            }
        } else if is_direct(b) {
            i += 1;
        } else {
            return Err(EncodingError::new(i, Some(1)));
        }
    }

    Ok(())
}

/// Decode a character at the given offset.
fn decode_char_at_utf7<C: Utf7Config>(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
    if offset >= bytes.len() {
        return None;
    }

    // Determine state at offset
    let (state, base64_start) = state_at_offset_utf7::<C>(bytes, offset)?;
    let is_direct = if C::SHIFT_CHAR == b'+' {
        is_direct_std
    } else {
        is_direct_imap
    };

    match state {
        State::Direct => {
            let b = bytes[offset];
            if b == C::SHIFT_CHAR {
                // Check if this is shift-char followed by '-' (literal)
                if offset + 1 < bytes.len() && bytes[offset + 1] == b'-' {
                    return Some((C::SHIFT_CHAR as char, offset + 2));
                }
                // Start of Base64 sequence - decode first character
                return decode_first_from_base64::<C>(bytes, offset);
            }
            if is_direct(b) {
                return Some((b as char, offset + 1));
            }
            None
        }
        State::Base64 => {
            // We're in the middle of a Base64 sequence
            // Need to decode from the start of the sequence
            decode_char_in_base64::<C>(bytes, base64_start, offset)
        }
    }
}

/// Determine the state at a given offset.
fn state_at_offset_utf7<C: Utf7Config>(bytes: &[u8], offset: usize) -> Option<(State, usize)> {
    let is_direct = if C::SHIFT_CHAR == b'+' {
        is_direct_std
    } else {
        is_direct_imap
    };
    let mut state = State::Direct;
    let mut base64_start = 0;
    let mut i = 0;

    while i < offset {
        if i >= bytes.len() {
            break;
        }

        let b = bytes[i];

        match state {
            State::Direct => {
                if b == C::SHIFT_CHAR {
                    if i + 1 < bytes.len() && bytes[i + 1] == b'-' {
                        // Literal shift char
                        i += 2;
                    } else {
                        // Enter Base64 mode
                        state = State::Base64;
                        base64_start = i + 1;
                        i += 1;
                    }
                } else if is_direct(b) {
                    i += 1;
                } else {
                    return None;
                }
            }
            State::Base64 => {
                if b == b'-' {
                    // Explicit end of Base64
                    state = State::Direct;
                    i += 1;
                } else if base64_decode(b, C::BASE64_ALPHABET).is_some() {
                    i += 1;
                } else if is_direct(b) {
                    // Implicit end of Base64
                    state = State::Direct;
                    // Don't advance i - the direct char will be processed next
                } else {
                    return None;
                }
            }
        }
    }

    Some((state, base64_start))
}

/// Decode the first character from a Base64 sequence starting at shift_pos.
fn decode_first_from_base64<C: Utf7Config>(
    bytes: &[u8],
    shift_pos: usize,
) -> Option<(char, usize)> {
    let is_direct = if C::SHIFT_CHAR == b'+' {
        is_direct_std
    } else {
        is_direct_imap
    };

    let mut i = shift_pos + 1; // Skip the shift character
    let mut base64_bits: u32 = 0;
    let mut bit_count = 0;
    let mut first_code_unit: Option<u16> = None;

    while i < bytes.len() {
        let b = bytes[i];

        if b == b'-' {
            i += 1;
            break;
        }

        if let Some(val) = base64_decode(b, C::BASE64_ALPHABET) {
            base64_bits = (base64_bits << 6) | val as u32;
            bit_count += 6;
            i += 1;

            // Extract first code unit
            if bit_count >= 16 && first_code_unit.is_none() {
                bit_count -= 16;
                first_code_unit = Some(((base64_bits >> bit_count) & 0xFFFF) as u16);

                // Check if this is a high surrogate
                if let Some(cu) = first_code_unit {
                    if (0xD800..=0xDBFF).contains(&cu) {
                        // Need to get the low surrogate too
                        continue;
                    }
                }
                break;
            }

            // If we have a high surrogate, keep going for the low surrogate
            if let Some(cu) = first_code_unit {
                if (0xD800..=0xDBFF).contains(&cu) && bit_count >= 16 {
                    bit_count -= 16;
                    let low_cu = ((base64_bits >> bit_count) & 0xFFFF) as u16;
                    if (0xDC00..=0xDFFF).contains(&low_cu) {
                        // Combine surrogate pair
                        let high = (cu - 0xD800) as u32;
                        let low = (low_cu - 0xDC00) as u32;
                        let cp = 0x10000 + ((high << 10) | low);
                        return char::from_u32(cp).map(|c| (c, i));
                    }
                }
            }
        } else if is_direct(b) {
            // Implicit end
            break;
        } else {
            return None;
        }
    }

    // Convert single code unit to char
    first_code_unit.and_then(|cu| {
        if (0xD800..=0xDFFF).contains(&cu) {
            None // Lone surrogate
        } else {
            char::from_u32(cu as u32).map(|c| (c, i))
        }
    })
}

/// Decode a character within a Base64 sequence.
fn decode_char_in_base64<C: Utf7Config>(
    bytes: &[u8],
    base64_start: usize,
    target_offset: usize,
) -> Option<(char, usize)> {
    let is_direct = if C::SHIFT_CHAR == b'+' {
        is_direct_std
    } else {
        is_direct_imap
    };

    let mut i = base64_start;
    let mut base64_bits: u32 = 0;
    let mut bit_count = 0;
    let mut char_byte_start = base64_start;
    let mut code_units: Vec<u16> = Vec::new();

    while i < bytes.len() {
        let b = bytes[i];

        if b == b'-' {
            i += 1;
            break;
        }

        if let Some(val) = base64_decode(b, C::BASE64_ALPHABET) {
            base64_bits = (base64_bits << 6) | val as u32;
            bit_count += 6;
            i += 1;

            while bit_count >= 16 {
                bit_count -= 16;
                let cu = ((base64_bits >> bit_count) & 0xFFFF) as u16;
                code_units.push(cu);

                // Check if we've reached or passed the target
                if i > target_offset || (i == target_offset && bit_count == 0) {
                    // Decode accumulated code units
                    return decode_code_units(&code_units, char_byte_start, i);
                }

                // If this completes a character, update char_byte_start
                let len = code_units.len();
                if len > 0 {
                    let last = code_units[len - 1];
                    if !(0xD800..=0xDBFF).contains(&last) && !(0xDC00..=0xDFFF).contains(&last) {
                        // Complete BMP character
                        char_byte_start = i;
                        code_units.clear();
                    } else if (0xDC00..=0xDFFF).contains(&last) && len >= 2 {
                        // Complete surrogate pair
                        char_byte_start = i;
                        code_units.clear();
                    }
                }
            }
        } else if is_direct(b) {
            break;
        } else {
            return None;
        }
    }

    // Handle any remaining code units
    if !code_units.is_empty() {
        return decode_code_units(&code_units, char_byte_start, i);
    }

    None
}

/// Decode a sequence of UTF-16 code units into a character.
fn decode_code_units(
    code_units: &[u16],
    _byte_start: usize,
    byte_end: usize,
) -> Option<(char, usize)> {
    if code_units.is_empty() {
        return None;
    }

    let cu = code_units[0];

    // Check for surrogate pair
    if (0xD800..=0xDBFF).contains(&cu) {
        if code_units.len() < 2 {
            return None;
        }
        let cu2 = code_units[1];
        if !(0xDC00..=0xDFFF).contains(&cu2) {
            return None;
        }
        let high = (cu - 0xD800) as u32;
        let low = (cu2 - 0xDC00) as u32;
        let cp = 0x10000 + ((high << 10) | low);
        return char::from_u32(cp).map(|c| (c, byte_end));
    }

    if (0xDC00..=0xDFFF).contains(&cu) {
        return None; // Lone low surrogate
    }

    char::from_u32(cu as u32).map(|c| (c, byte_end))
}

/// Encode a character to UTF-7.
fn encode_char_utf7<C: Utf7Config>(c: char, buf: &mut [u8]) -> usize {
    let cp = c as u32;

    // Check if it's a direct character
    let is_direct = if C::SHIFT_CHAR == b'+' {
        is_direct_std
    } else {
        is_direct_imap
    };

    if cp < 0x80 && is_direct(cp as u8) {
        buf[0] = cp as u8;
        return 1;
    }

    // Literal shift character
    if cp == C::SHIFT_CHAR as u32 {
        buf[0] = C::SHIFT_CHAR;
        buf[1] = b'-';
        return 2;
    }

    // Encode in Base64
    buf[0] = C::SHIFT_CHAR;
    let mut pos = 1;

    // Get UTF-16 representation
    let mut utf16 = [0u16; 2];
    let utf16_len = c.encode_utf16(&mut utf16).len();

    // Encode UTF-16BE as Base64
    let mut bits: u32 = 0;
    let mut bit_count = 0;

    for i in 0..utf16_len {
        let cu = utf16[i];
        bits = (bits << 16) | cu as u32;
        bit_count += 16;

        while bit_count >= 6 {
            bit_count -= 6;
            let idx = ((bits >> bit_count) & 0x3F) as usize;
            buf[pos] = C::BASE64_ALPHABET[idx];
            pos += 1;
        }
    }

    // Flush remaining bits with padding
    if bit_count > 0 {
        let idx = ((bits << (6 - bit_count)) & 0x3F) as usize;
        buf[pos] = C::BASE64_ALPHABET[idx];
        pos += 1;
    }

    // End marker
    buf[pos] = b'-';
    pos += 1;

    pos
}

/// Calculate encoded length for a character.
fn encoded_len_utf7<C: Utf7Config>(c: char) -> usize {
    let cp = c as u32;

    let is_direct = if C::SHIFT_CHAR == b'+' {
        is_direct_std
    } else {
        is_direct_imap
    };

    if cp < 0x80 && is_direct(cp as u8) {
        return 1;
    }

    if cp == C::SHIFT_CHAR as u32 {
        return 2; // +-
    }

    // shift + base64 + terminator
    // UTF-16 code units: 1 for BMP, 2 for supplementary
    // Each 16 bits needs ceil(16/6) = 3 base64 chars
    // Plus shift char and terminator
    let utf16_len = c.len_utf16();
    let bits = utf16_len * 16;
    let base64_chars = (bits + 5) / 6; // ceil(bits / 6)
    1 + base64_chars + 1 // shift + base64 + '-'
}

// Implement Encoding for Utf7
impl Encoding for Utf7 {
    const NAME: &'static str = "UTF-7";
    const IS_FIXED_WIDTH: bool = false;
    const BYTES_PER_CHAR: Option<usize> = None;
    const MAX_CHAR_LEN: usize = 8; // + 6 base64 chars + -

    fn validate(bytes: &[u8]) -> Result<(), EncodingError> {
        validate_utf7::<Self>(bytes)
    }

    fn decode_char_at(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        decode_char_at_utf7::<Self>(bytes, offset)
    }

    fn encoded_len(c: char) -> usize {
        encoded_len_utf7::<Self>(c)
    }

    fn encode_char(c: char, buf: &mut [u8]) -> usize {
        encode_char_utf7::<Self>(c, buf)
    }

    fn is_char_boundary(bytes: &[u8], index: usize) -> bool {
        if index == 0 || index >= bytes.len() {
            return index <= bytes.len();
        }

        // Check state at this position
        if let Some((state, _)) = state_at_offset_utf7::<Self>(bytes, index) {
            match state {
                State::Direct => {
                    // In direct mode, every byte is a boundary unless it's the '-' after shift
                    if index > 0 && bytes[index - 1] == Self::SHIFT_CHAR && bytes[index] == b'-' {
                        return false;
                    }
                    true
                }
                State::Base64 => {
                    // In Base64 mode, boundaries are complex
                    // For simplicity, we say boundaries are only at the start of the sequence
                    false
                }
            }
        } else {
            false
        }
    }

    fn decode_char_before(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        if offset == 0 || offset > bytes.len() {
            return None;
        }

        // Scan from the beginning to find all characters
        let mut i = 0;
        let mut last_char_start = 0;
        let mut last_char: Option<char> = None;

        while i < offset {
            if let Some((c, next)) = Self::decode_char_at(bytes, i) {
                last_char_start = i;
                last_char = Some(c);
                i = next;
            } else {
                i += 1;
            }
        }

        last_char.map(|c| (c, last_char_start))
    }
}

impl UniversalEncoding for Utf7 {}

// Implement Encoding for Utf7Imap
impl Encoding for Utf7Imap {
    const NAME: &'static str = "UTF-7-IMAP";
    const IS_FIXED_WIDTH: bool = false;
    const BYTES_PER_CHAR: Option<usize> = None;
    const MAX_CHAR_LEN: usize = 8;

    fn validate(bytes: &[u8]) -> Result<(), EncodingError> {
        validate_utf7::<Self>(bytes)
    }

    fn decode_char_at(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        decode_char_at_utf7::<Self>(bytes, offset)
    }

    fn encoded_len(c: char) -> usize {
        encoded_len_utf7::<Self>(c)
    }

    fn encode_char(c: char, buf: &mut [u8]) -> usize {
        encode_char_utf7::<Self>(c, buf)
    }

    fn is_char_boundary(bytes: &[u8], index: usize) -> bool {
        if index == 0 || index >= bytes.len() {
            return index <= bytes.len();
        }

        if let Some((state, _)) = state_at_offset_utf7::<Self>(bytes, index) {
            match state {
                State::Direct => {
                    if index > 0 && bytes[index - 1] == Self::SHIFT_CHAR && bytes[index] == b'-' {
                        return false;
                    }
                    true
                }
                State::Base64 => false,
            }
        } else {
            false
        }
    }

    fn decode_char_before(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        if offset == 0 || offset > bytes.len() {
            return None;
        }

        let mut i = 0;
        let mut last_char_start = 0;
        let mut last_char: Option<char> = None;

        while i < offset {
            if let Some((c, next)) = Self::decode_char_at(bytes, i) {
                last_char_start = i;
                last_char = Some(c);
                i = next;
            } else {
                i += 1;
            }
        }

        last_char.map(|c| (c, last_char_start))
    }
}

impl UniversalEncoding for Utf7Imap {}

#[cfg(feature = "registry")]
inventory::submit! {
    crate::registry::EncodingEntry {
        name: "UTF-7",
        aliases: &["UTF7", "utf-7", "utf7"],
        is_unicode: true,
        decode: |bytes| {
            Utf7::validate(bytes)?;
            let mut result = Vec::new();
            let mut offset = 0;
            while let Some((c, next)) = Utf7::decode_char_at(bytes, offset) {
                result.push(c);
                offset = next;
            }
            Ok(result)
        },
        try_encode_char: |c| {
            let mut buf = [0u8; 8];
            let len = Utf7::encode_char(c, &mut buf);
            Some(buf[..len].to_vec())
        },
    }
}

#[cfg(feature = "registry")]
inventory::submit! {
    crate::registry::EncodingEntry {
        name: "UTF-7-IMAP",
        aliases: &["UTF7-IMAP", "utf-7-imap", "utf7-imap"],
        is_unicode: true,
        decode: |bytes| {
            Utf7Imap::validate(bytes)?;
            let mut result = Vec::new();
            let mut offset = 0;
            while let Some((c, next)) = Utf7Imap::decode_char_at(bytes, offset) {
                result.push(c);
                offset = next;
            }
            Ok(result)
        },
        try_encode_char: |c| {
            let mut buf = [0u8; 8];
            let len = Utf7Imap::encode_char(c, &mut buf);
            Some(buf[..len].to_vec())
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ascii() {
        // ASCII should pass through directly
        assert!(Utf7::validate(b"Hello World").is_ok());

        let (c, next) = Utf7::decode_char_at(b"Hello", 0).unwrap();
        assert_eq!(c, 'H');
        assert_eq!(next, 1);
    }

    #[test]
    fn test_literal_plus() {
        // +- encodes a literal +
        let bytes = b"A+-B";
        assert!(Utf7::validate(bytes).is_ok());

        let (c, next) = Utf7::decode_char_at(bytes, 0).unwrap();
        assert_eq!(c, 'A');
        assert_eq!(next, 1);

        let (c, next) = Utf7::decode_char_at(bytes, 1).unwrap();
        assert_eq!(c, '+');
        assert_eq!(next, 3);

        let (c, _) = Utf7::decode_char_at(bytes, 3).unwrap();
        assert_eq!(c, 'B');
    }

    #[test]
    fn test_encode_ascii() {
        let mut buf = [0u8; 8];
        let len = Utf7::encode_char('A', &mut buf);
        assert_eq!(len, 1);
        assert_eq!(buf[0], b'A');
    }

    #[test]
    fn test_encode_plus() {
        let mut buf = [0u8; 8];
        let len = Utf7::encode_char('+', &mut buf);
        assert_eq!(len, 2);
        assert_eq!(&buf[..2], b"+-");
    }

    #[test]
    fn test_encode_non_ascii() {
        // é is U+00E9
        let mut buf = [0u8; 8];
        let len = Utf7::encode_char('é', &mut buf);
        assert!(len > 2); // +base64-

        // Verify it round-trips
        assert!(Utf7::validate(&buf[..len]).is_ok());
        let (c, _) = Utf7::decode_char_at(&buf[..len], 0).unwrap();
        assert_eq!(c, 'é');
    }

    #[test]
    fn test_encode_japanese() {
        // あ is U+3042
        let mut buf = [0u8; 8];
        let len = Utf7::encode_char('あ', &mut buf);

        // Round-trip
        assert!(Utf7::validate(&buf[..len]).is_ok());
        let (c, _) = Utf7::decode_char_at(&buf[..len], 0).unwrap();
        assert_eq!(c, 'あ');
    }

    #[test]
    fn test_imap_literal_ampersand() {
        // &- encodes a literal &
        let bytes = b"A&-B";
        assert!(Utf7Imap::validate(bytes).is_ok());

        let (c, next) = Utf7Imap::decode_char_at(bytes, 0).unwrap();
        assert_eq!(c, 'A');
        assert_eq!(next, 1);

        let (c, next) = Utf7Imap::decode_char_at(bytes, 1).unwrap();
        assert_eq!(c, '&');
        assert_eq!(next, 3);
    }

    #[test]
    fn test_imap_encode() {
        let mut buf = [0u8; 8];

        // Literal &
        let len = Utf7Imap::encode_char('&', &mut buf);
        assert_eq!(len, 2);
        assert_eq!(&buf[..2], b"&-");

        // Non-ASCII
        let len = Utf7Imap::encode_char('é', &mut buf);
        assert!(Utf7Imap::validate(&buf[..len]).is_ok());
        let (c, _) = Utf7Imap::decode_char_at(&buf[..len], 0).unwrap();
        assert_eq!(c, 'é');
    }

    #[test]
    fn test_supplementary_char() {
        // 😀 is U+1F600 (requires surrogate pair in UTF-16)
        let mut buf = [0u8; 12];
        let len = Utf7::encode_char('😀', &mut buf);

        // Round-trip
        assert!(Utf7::validate(&buf[..len]).is_ok());
        let (c, _) = Utf7::decode_char_at(&buf[..len], 0).unwrap();
        assert_eq!(c, '😀');
    }

    #[test]
    fn test_encoded_len() {
        assert_eq!(Utf7::encoded_len('A'), 1);
        assert_eq!(Utf7::encoded_len('+'), 2);
        // Non-ASCII needs shift + base64 + terminator
        assert!(Utf7::encoded_len('é') > 2);
    }
}
