//! Big5 encoding.
//!
//! Big5 is a variable-width encoding used for Traditional Chinese text,
//! primarily in Taiwan, Hong Kong, and Macau. It is compatible with ASCII
//! and uses 2-byte sequences for Chinese characters.
//!
//! # Structure
//!
//! Big5 uses variable-width encoding:
//! - 1 byte: ASCII (0x00-0x7F)
//! - 2 bytes: Chinese characters (lead 0x81-0xFE, trail 0x40-0x7E or 0xA1-0xFE)
//!
//! The WHATWG variant (used here) includes extensions for Hong Kong
//! Supplementary Character Set (HKSCS).

use alloc::vec::Vec;

use crate::encoding::Encoding;
use crate::error::EncodingError;

// Include generated tables
include!(concat!(env!("OUT_DIR"), "/big5_tables.rs"));

/// Big5 encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Big5;

/// Look up a character by pointer in the decode table.
fn big5_lookup(pointer: u16) -> Option<char> {
    BIG5_DECODE
        .binary_search_by_key(&pointer, |&(p, _)| p)
        .ok()
        .map(|idx| BIG5_DECODE[idx].1)
}

/// Look up a pointer by character in the encode table.
fn big5_encode_lookup(c: char) -> Option<u16> {
    BIG5_ENCODE
        .binary_search_by_key(&c, |&(ch, _)| ch)
        .ok()
        .map(|idx| BIG5_ENCODE[idx].1)
}

/// Check if a byte is a valid trail byte in Big5.
#[inline]
fn is_valid_trail(b: u8) -> bool {
    (0x40..=0x7E).contains(&b) || (0xA1..=0xFE).contains(&b)
}

impl Encoding for Big5 {
    const NAME: &'static str = "Big5";
    const IS_FIXED_WIDTH: bool = false;
    const BYTES_PER_CHAR: Option<usize> = None;
    const MAX_CHAR_LEN: usize = 2;

    fn validate(bytes: &[u8]) -> Result<(), EncodingError> {
        let mut i = 0;
        while i < bytes.len() {
            let b1 = bytes[i];

            if b1 < 0x80 {
                // ASCII
                i += 1;
            } else if (0x81..=0xFE).contains(&b1) {
                // Lead byte of 2-byte sequence
                if i + 1 >= bytes.len() {
                    return Err(EncodingError::new(i, Some(1)));
                }
                let b2 = bytes[i + 1];
                if !is_valid_trail(b2) {
                    return Err(EncodingError::new(i, Some(2)));
                }
                // Validate the sequence maps to a valid character
                let pointer = pointer_from_bytes(b1, b2);
                if big5_lookup(pointer).is_none() {
                    return Err(EncodingError::new(i, Some(2)));
                }
                i += 2;
            } else {
                return Err(EncodingError::new(i, Some(1)));
            }
        }
        Ok(())
    }

    fn decode_char_at(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        let b1 = *bytes.get(offset)?;

        // ASCII (0x00-0x7F)
        if b1 < 0x80 {
            return Some((b1 as char, offset + 1));
        }

        // 2-byte sequence (lead 0x81-0xFE)
        if (0x81..=0xFE).contains(&b1) {
            let b2 = *bytes.get(offset + 1)?;
            if !is_valid_trail(b2) {
                return None;
            }
            let pointer = pointer_from_bytes(b1, b2);
            let c = big5_lookup(pointer)?;
            return Some((c, offset + 2));
        }

        None
    }

    fn encoded_len(c: char) -> usize {
        let cp = c as u32;

        // ASCII
        if cp < 0x80 {
            return 1;
        }

        // Everything else is 2 bytes (or unencodable)
        2
    }

    fn encode_char(c: char, buf: &mut [u8]) -> usize {
        let cp = c as u32;

        // ASCII
        if cp < 0x80 {
            buf[0] = cp as u8;
            return 1;
        }

        // Look up in encode table
        if let Some(pointer) = big5_encode_lookup(c) {
            let (b1, b2) = bytes_from_pointer(pointer);
            buf[0] = b1;
            buf[1] = b2;
            return 2;
        }

        panic!("character '{}' cannot be encoded in Big5", c);
    }

    fn try_encode_char(c: char, buf: &mut [u8]) -> Option<usize> {
        let cp = c as u32;

        // ASCII
        if cp < 0x80 {
            buf[0] = cp as u8;
            return Some(1);
        }

        // Look up in encode table
        let pointer = big5_encode_lookup(c)?;
        let (b1, b2) = bytes_from_pointer(pointer);
        buf[0] = b1;
        buf[1] = b2;
        Some(2)
    }

    fn can_encode(c: char) -> bool {
        let cp = c as u32;
        if cp < 0x80 {
            return true;
        }
        big5_encode_lookup(c).is_some()
    }

    fn is_char_boundary(bytes: &[u8], index: usize) -> bool {
        if index == 0 || index >= bytes.len() {
            return index <= bytes.len();
        }

        // Scan backward to find an anchor (start of buffer or ASCII byte)
        let mut anchor = index;
        while anchor > 0 && bytes[anchor - 1] >= 0x80 {
            anchor -= 1;
        }

        // From anchor, parse forward to determine character boundaries
        let mut pos = anchor;
        while pos < index {
            let b = bytes[pos];
            if b < 0x80 {
                // ASCII - single byte
                pos += 1;
            } else if (0x81..=0xFE).contains(&b)
                && pos + 1 < bytes.len()
                && is_valid_trail(bytes[pos + 1])
            {
                // Valid 2-byte sequence
                pos += 2;
            } else {
                // Invalid or incomplete - treat as single byte boundary
                pos += 1;
            }
        }

        pos == index
    }

    fn decode_char_before(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        if offset == 0 || offset > bytes.len() {
            return None;
        }

        let b = bytes[offset - 1];

        // Try 1-byte (ASCII) first
        if b < 0x80 {
            return Some((b as char, offset - 1));
        }

        // Try 2-byte sequence
        if offset >= 2 && is_valid_trail(b) {
            let b1 = bytes[offset - 2];
            if (0x81..=0xFE).contains(&b1) {
                let pointer = pointer_from_bytes(b1, b);
                if let Some(c) = big5_lookup(pointer) {
                    return Some((c, offset - 2));
                }
            }
        }

        None
    }
}

/// Convert lead and trail bytes to a WHATWG pointer.
///
/// WHATWG Big5 pointer formula:
/// offset = trail < 0x7F ? trail - 0x40 : trail - 0x62
/// pointer = (lead - 0x81) * 157 + offset
#[inline]
fn pointer_from_bytes(lead: u8, trail: u8) -> u16 {
    let offset = if trail < 0x7F {
        trail - 0x40
    } else {
        trail - 0x62
    };
    ((lead - 0x81) as u16) * 157 + offset as u16
}

/// Convert a WHATWG pointer back to lead and trail bytes.
#[inline]
fn bytes_from_pointer(pointer: u16) -> (u8, u8) {
    let lead = (pointer / 157) as u8 + 0x81;
    let offset = (pointer % 157) as u8;
    let trail = if offset < 0x3F {
        offset + 0x40
    } else {
        offset + 0x62
    };
    (lead, trail)
}

impl crate::encoding::LimitedEncoding for Big5 {}

#[cfg(feature = "registry")]
inventory::submit! {
    crate::registry::EncodingEntry {
        name: "Big5",
        aliases: &["big5", "BIG5", "Big-5", "big-5", "csBig5", "Windows-950", "windows-950", "cp950", "CP950"],
        is_unicode: false,
        decode: |bytes| {
            Big5::validate(bytes)?;
            let mut chars = Vec::new();
            let mut offset = 0;
            while let Some((c, next)) = Big5::decode_char_at(bytes, offset) {
                chars.push(c);
                offset = next;
            }
            Ok(chars)
        },
        try_encode_char: |c| {
            let mut buf = [0u8; 2];
            Big5::try_encode_char(c, &mut buf).map(|len| buf[..len].to_vec())
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ascii() {
        let bytes = b"Hello";
        assert!(Big5::validate(bytes).is_ok());

        let (c, next) = Big5::decode_char_at(bytes, 0).unwrap();
        assert_eq!(c, 'H');
        assert_eq!(next, 1);
    }

    #[test]
    fn test_chinese() {
        // 中 (U+4E2D) - "middle/center"
        let mut buf = [0u8; 2];
        if Big5::can_encode('中') {
            let len = Big5::encode_char('中', &mut buf);
            assert_eq!(len, 2);

            let (c, _) = Big5::decode_char_at(&buf, 0).unwrap();
            assert_eq!(c, '中');
        }
    }

    #[test]
    fn test_roundtrip() {
        let test_chars = ['A', '中', '文', '字', '台', '灣'];
        for &c in &test_chars {
            if Big5::can_encode(c) {
                let mut buf = [0u8; 4];
                let len = Big5::encode_char(c, &mut buf);
                let (decoded, _) = Big5::decode_char_at(&buf[..len], 0).unwrap();
                assert_eq!(c, decoded, "Roundtrip failed for '{}'", c);
            }
        }
    }

    #[test]
    fn test_validate() {
        // Valid ASCII
        assert!(Big5::validate(b"Hello").is_ok());

        // Invalid: lone lead byte
        assert!(Big5::validate(&[0x81]).is_err());

        // Invalid: bad trail byte (0x7F is not valid)
        assert!(Big5::validate(&[0x81, 0x7F]).is_err());
    }

    #[test]
    fn test_is_char_boundary() {
        // 中文 in Big5
        let s: crate::String<Big5> = "中文".chars().collect();
        let bytes = s.as_bytes();

        assert!(Big5::is_char_boundary(bytes, 0));
        assert!(!Big5::is_char_boundary(bytes, 1));
        assert!(Big5::is_char_boundary(bytes, 2));
        assert!(!Big5::is_char_boundary(bytes, 3));
        assert!(Big5::is_char_boundary(bytes, 4));
    }

    #[test]
    fn test_decode_char_before() {
        let s: crate::String<Big5> = "A中B".chars().collect();
        let bytes = s.as_bytes();

        // From end
        let (c, pos) = Big5::decode_char_before(bytes, bytes.len()).unwrap();
        assert_eq!(c, 'B');

        let (c, pos) = Big5::decode_char_before(bytes, pos).unwrap();
        assert_eq!(c, '中');

        let (c, _) = Big5::decode_char_before(bytes, pos).unwrap();
        assert_eq!(c, 'A');
    }
}
