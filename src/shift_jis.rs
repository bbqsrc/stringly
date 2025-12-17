//! Shift_JIS encoding.
//!
//! Shift_JIS is a variable-width encoding used for Japanese text, primarily
//! on Windows systems. It is compatible with JIS X 0201 (ASCII + half-width
//! katakana) and JIS X 0208 (Japanese characters).
//!
//! # Structure
//!
//! Shift_JIS uses variable-width encoding:
//! - 1 byte: ASCII (0x00-0x7F, except 0x5C and 0x7E which may vary)
//! - 1 byte: Half-width katakana (0xA1-0xDF)
//! - 2 bytes: JIS X 0208 (lead 0x81-0x9F or 0xE0-0xFC, trail 0x40-0x7E or 0x80-0xFC)
//!
//! This implementation follows the WHATWG encoding standard.

use crate::encoding::Encoding;
use crate::error::EncodingError;

// Include generated JIS X 0208 tables (shared with EUC-JP)
include!(concat!(env!("OUT_DIR"), "/jis0208_tables.rs"));

/// Shift_JIS encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct ShiftJis;

/// Look up a character by pointer in the JIS X 0208 decode table.
fn jis0208_lookup(pointer: u16) -> Option<char> {
    JIS0208_DECODE
        .binary_search_by_key(&pointer, |&(p, _)| p)
        .ok()
        .map(|idx| JIS0208_DECODE[idx].1)
}

/// Look up a pointer by character in the JIS X 0208 encode table.
fn jis0208_encode_lookup(c: char) -> Option<u16> {
    JIS0208_ENCODE
        .binary_search_by_key(&c, |&(ch, _)| ch)
        .ok()
        .map(|idx| JIS0208_ENCODE[idx].1)
}

/// Check if a byte is a valid lead byte in Shift_JIS.
#[inline]
fn is_lead_byte(b: u8) -> bool {
    (0x81..=0x9F).contains(&b) || (0xE0..=0xFC).contains(&b)
}

/// Check if a byte is a valid trail byte in Shift_JIS.
#[inline]
fn is_trail_byte(b: u8) -> bool {
    (0x40..=0x7E).contains(&b) || (0x80..=0xFC).contains(&b)
}

impl Encoding for ShiftJis {
    const NAME: &'static str = "Shift_JIS";
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
            } else if (0xA1..=0xDF).contains(&b1) {
                // Half-width katakana (single byte)
                i += 1;
            } else if is_lead_byte(b1) {
                // Lead byte of 2-byte sequence
                if i + 1 >= bytes.len() {
                    return Err(EncodingError::new(i, Some(1)));
                }
                let b2 = bytes[i + 1];
                if !is_trail_byte(b2) {
                    return Err(EncodingError::new(i, Some(2)));
                }
                // Validate the sequence maps to a valid character
                let pointer = pointer_from_bytes(b1, b2);
                if jis0208_lookup(pointer).is_none() {
                    return Err(EncodingError::new(i, Some(2)));
                }
                i += 2;
            } else if b1 == 0x80 || (0xA0..=0xA0).contains(&b1) || b1 > 0xFC {
                // Invalid single bytes
                return Err(EncodingError::new(i, Some(1)));
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

        // Half-width katakana (0xA1-0xDF) -> U+FF61-U+FF9F
        if (0xA1..=0xDF).contains(&b1) {
            let c = char::from_u32(0xFF61 + (b1 - 0xA1) as u32)?;
            return Some((c, offset + 1));
        }

        // 2-byte JIS X 0208 sequence
        if is_lead_byte(b1) {
            let b2 = *bytes.get(offset + 1)?;
            if !is_trail_byte(b2) {
                return None;
            }
            let pointer = pointer_from_bytes(b1, b2);
            let c = jis0208_lookup(pointer)?;
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

        // Half-width katakana (U+FF61-U+FF9F)
        if (0xFF61..=0xFF9F).contains(&cp) {
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

        // Half-width katakana (U+FF61-U+FF9F) -> 0xA1-0xDF
        if (0xFF61..=0xFF9F).contains(&cp) {
            buf[0] = (cp - 0xFF61 + 0xA1) as u8;
            return 1;
        }

        // Look up in JIS X 0208 encode table
        if let Some(pointer) = jis0208_encode_lookup(c) {
            let (b1, b2) = bytes_from_pointer(pointer);
            buf[0] = b1;
            buf[1] = b2;
            return 2;
        }

        panic!("character '{}' cannot be encoded in Shift_JIS", c);
    }

    fn try_encode_char(c: char, buf: &mut [u8]) -> Option<usize> {
        let cp = c as u32;

        // ASCII
        if cp < 0x80 {
            buf[0] = cp as u8;
            return Some(1);
        }

        // Half-width katakana (U+FF61-U+FF9F) -> 0xA1-0xDF
        if (0xFF61..=0xFF9F).contains(&cp) {
            buf[0] = (cp - 0xFF61 + 0xA1) as u8;
            return Some(1);
        }

        // Look up in JIS X 0208 encode table
        let pointer = jis0208_encode_lookup(c)?;
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
        if (0xFF61..=0xFF9F).contains(&cp) {
            return true;
        }
        jis0208_encode_lookup(c).is_some()
    }

    fn is_char_boundary(bytes: &[u8], index: usize) -> bool {
        if index == 0 || index >= bytes.len() {
            return index <= bytes.len();
        }

        // Scan backward to find an anchor (start of buffer, ASCII, or half-width katakana)
        let mut anchor = index;
        while anchor > 0 {
            let b = bytes[anchor - 1];
            if b < 0x80 || (0xA1..=0xDF).contains(&b) {
                // ASCII or half-width katakana - this is a boundary
                break;
            }
            anchor -= 1;
        }

        // From anchor, parse forward to determine character boundaries
        let mut pos = anchor;
        while pos < index {
            let b = bytes[pos];
            if b < 0x80 {
                // ASCII - single byte
                pos += 1;
            } else if (0xA1..=0xDF).contains(&b) {
                // Half-width katakana - single byte
                pos += 1;
            } else if is_lead_byte(b) && pos + 1 < bytes.len() && is_trail_byte(bytes[pos + 1]) {
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

        // ASCII
        if b < 0x80 {
            return Some((b as char, offset - 1));
        }

        // Half-width katakana (single byte)
        if (0xA1..=0xDF).contains(&b) {
            let c = char::from_u32(0xFF61 + (b - 0xA1) as u32)?;
            return Some((c, offset - 1));
        }

        // Try 2-byte sequence if current byte could be a trail byte
        if offset >= 2 && is_trail_byte(b) {
            let b1 = bytes[offset - 2];
            if is_lead_byte(b1) {
                let pointer = pointer_from_bytes(b1, b);
                if let Some(c) = jis0208_lookup(pointer) {
                    return Some((c, offset - 2));
                }
            }
        }

        None
    }
}

/// Convert Shift_JIS lead and trail bytes to a JIS X 0208 pointer.
///
/// Shift_JIS to pointer formula:
/// lead_offset = lead < 0xA0 ? lead - 0x81 : lead - 0xC1
/// trail_offset = trail < 0x7F ? trail - 0x40 : trail - 0x41
/// pointer = lead_offset * 188 + trail_offset
#[inline]
fn pointer_from_bytes(lead: u8, trail: u8) -> u16 {
    let lead_offset = if lead < 0xA0 {
        lead - 0x81
    } else {
        lead - 0xC1
    };
    let trail_offset = if trail < 0x7F {
        trail - 0x40
    } else {
        trail - 0x41
    };
    (lead_offset as u16) * 188 + trail_offset as u16
}

/// Convert a JIS X 0208 pointer to Shift_JIS lead and trail bytes.
#[inline]
fn bytes_from_pointer(pointer: u16) -> (u8, u8) {
    let lead_offset = (pointer / 188) as u8;
    let trail_offset = (pointer % 188) as u8;

    let lead = if lead_offset < 0x1F {
        lead_offset + 0x81
    } else {
        lead_offset + 0xC1
    };

    let trail = if trail_offset < 0x3F {
        trail_offset + 0x40
    } else {
        trail_offset + 0x41
    };

    (lead, trail)
}

impl crate::encoding::LimitedEncoding for ShiftJis {}

#[cfg(feature = "registry")]
inventory::submit! {
    crate::registry::EncodingEntry {
        name: "Shift_JIS",
        aliases: &["shift_jis", "shift-jis", "ShiftJIS", "shiftjis", "SJIS", "sjis", "Windows-932", "windows-932", "cp932", "CP932"],
        is_unicode: false,
        decode: |bytes| {
            ShiftJis::validate(bytes)?;
            let mut chars = Vec::new();
            let mut offset = 0;
            while let Some((c, next)) = ShiftJis::decode_char_at(bytes, offset) {
                chars.push(c);
                offset = next;
            }
            Ok(chars)
        },
        try_encode_char: |c| {
            let mut buf = [0u8; 2];
            ShiftJis::try_encode_char(c, &mut buf).map(|len| buf[..len].to_vec())
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ascii() {
        let bytes = b"Hello";
        assert!(ShiftJis::validate(bytes).is_ok());

        let (c, next) = ShiftJis::decode_char_at(bytes, 0).unwrap();
        assert_eq!(c, 'H');
        assert_eq!(next, 1);
    }

    #[test]
    fn test_halfwidth_katakana() {
        // ｱ (U+FF71) - half-width katakana A
        // In Shift_JIS: 0xB1
        let bytes = [0xB1];
        assert!(ShiftJis::validate(&bytes).is_ok());

        let (c, next) = ShiftJis::decode_char_at(&bytes, 0).unwrap();
        assert_eq!(c, 'ｱ'); // U+FF71 half-width, not U+30A2 full-width
        assert_eq!(next, 1);

        // Roundtrip
        let mut buf = [0u8; 2];
        let len = ShiftJis::encode_char('ｱ', &mut buf);
        assert_eq!(len, 1);
        assert_eq!(buf[0], 0xB1);
    }

    #[test]
    fn test_japanese() {
        // 日 (U+65E5) - "day/sun"
        let mut buf = [0u8; 2];
        if ShiftJis::can_encode('日') {
            let len = ShiftJis::encode_char('日', &mut buf);
            assert_eq!(len, 2);

            let (c, _) = ShiftJis::decode_char_at(&buf, 0).unwrap();
            assert_eq!(c, '日');
        }
    }

    #[test]
    fn test_roundtrip() {
        let test_chars = ['A', '日', '本', '語', 'ア', 'イ'];
        for &c in &test_chars {
            if ShiftJis::can_encode(c) {
                let mut buf = [0u8; 4];
                let len = ShiftJis::encode_char(c, &mut buf);
                let (decoded, _) = ShiftJis::decode_char_at(&buf[..len], 0).unwrap();
                assert_eq!(c, decoded, "Roundtrip failed for '{}'", c);
            }
        }
    }

    #[test]
    fn test_validate() {
        // Valid ASCII
        assert!(ShiftJis::validate(b"Hello").is_ok());

        // Valid half-width katakana
        assert!(ShiftJis::validate(&[0xB1, 0xB2, 0xB3]).is_ok());

        // Invalid: lone lead byte
        assert!(ShiftJis::validate(&[0x81]).is_err());

        // Invalid byte 0x80
        assert!(ShiftJis::validate(&[0x80]).is_err());
    }

    #[test]
    fn test_is_char_boundary() {
        // 日本 in Shift_JIS
        let s: crate::String<ShiftJis> = "日本".chars().collect();
        let bytes = s.as_bytes();

        assert!(ShiftJis::is_char_boundary(bytes, 0));
        assert!(!ShiftJis::is_char_boundary(bytes, 1));
        assert!(ShiftJis::is_char_boundary(bytes, 2));
        assert!(!ShiftJis::is_char_boundary(bytes, 3));
        assert!(ShiftJis::is_char_boundary(bytes, 4));
    }

    #[test]
    fn test_decode_char_before() {
        let s: crate::String<ShiftJis> = "A日B".chars().collect();
        let bytes = s.as_bytes();

        // From end
        let (c, pos) = ShiftJis::decode_char_before(bytes, bytes.len()).unwrap();
        assert_eq!(c, 'B');

        let (c, pos) = ShiftJis::decode_char_before(bytes, pos).unwrap();
        assert_eq!(c, '日');

        let (c, _) = ShiftJis::decode_char_before(bytes, pos).unwrap();
        assert_eq!(c, 'A');
    }
}
