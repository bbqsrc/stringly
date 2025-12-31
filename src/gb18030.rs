//! GB18030 encoding.
//!
//! GB18030 is China's mandatory national standard encoding that covers all Unicode code points.
//! It is a superset of GBK/GB2312 and is backwards compatible with ASCII.
//!
//! # Structure
//!
//! GB18030 uses variable-width encoding:
//! - 1 byte: ASCII (0x00-0x7F)
//! - 2 bytes: GBK characters (lead: 0x81-0xFE, trail: 0x40-0x7E or 0x80-0xFE)
//! - 4 bytes: All other Unicode (B1: 0x81-0xFE, B2: 0x30-0x39, B3: 0x81-0xFE, B4: 0x30-0x39)

use alloc::vec::Vec;

use crate::encoding::Encoding;
use crate::error::EncodingError;

// Include generated tables
include!(concat!(env!("OUT_DIR"), "/gb18030_tables.rs"));

/// GB18030 encoding - China's mandatory national standard.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Gb18030;

impl Encoding for Gb18030 {
    const NAME: &'static str = "GB18030";
    const IS_FIXED_WIDTH: bool = false;
    const BYTES_PER_CHAR: Option<usize> = None;
    const MAX_CHAR_LEN: usize = 4;

    fn validate(bytes: &[u8]) -> Result<(), EncodingError> {
        let mut i = 0;
        while i < bytes.len() {
            let b1 = bytes[i];

            if b1 < 0x80 {
                // ASCII
                i += 1;
            } else if (0x81..=0xFE).contains(&b1) {
                if i + 1 >= bytes.len() {
                    return Err(EncodingError::new(i, Some(1)));
                }
                let b2 = bytes[i + 1];

                if (0x30..=0x39).contains(&b2) {
                    // 4-byte sequence
                    if i + 3 >= bytes.len() {
                        return Err(EncodingError::new(i, Some(bytes.len() - i)));
                    }
                    let b3 = bytes[i + 2];
                    let b4 = bytes[i + 3];

                    if !(0x81..=0xFE).contains(&b3) || !(0x30..=0x39).contains(&b4) {
                        return Err(EncodingError::new(i, Some(4)));
                    }

                    // Validate the 4-byte sequence maps to a valid codepoint
                    if decode_4byte(b1, b2, b3, b4).is_none() {
                        return Err(EncodingError::new(i, Some(4)));
                    }
                    i += 4;
                } else if (0x40..=0x7E).contains(&b2) || (0x80..=0xFE).contains(&b2) {
                    // 2-byte GBK sequence
                    if decode_2byte(b1, b2).is_none() {
                        return Err(EncodingError::new(i, Some(2)));
                    }
                    i += 2;
                } else {
                    return Err(EncodingError::new(i, Some(2)));
                }
            } else {
                return Err(EncodingError::new(i, Some(1)));
            }
        }
        Ok(())
    }

    fn decode_char_at(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        let b1 = *bytes.get(offset)?;

        // 1-byte: ASCII
        if b1 < 0x80 {
            return Some((b1 as char, offset + 1));
        }

        // Must be a lead byte
        if !(0x81..=0xFE).contains(&b1) {
            return None;
        }

        let b2 = *bytes.get(offset + 1)?;

        if (0x30..=0x39).contains(&b2) {
            // 4-byte sequence
            let b3 = *bytes.get(offset + 2)?;
            let b4 = *bytes.get(offset + 3)?;
            let c = decode_4byte(b1, b2, b3, b4)?;
            Some((c, offset + 4))
        } else if (0x40..=0x7E).contains(&b2) || (0x80..=0xFE).contains(&b2) {
            // 2-byte GBK sequence
            let c = decode_2byte(b1, b2)?;
            Some((c, offset + 2))
        } else {
            None
        }
    }

    fn encoded_len(c: char) -> usize {
        let cp = c as u32;

        // ASCII
        if cp < 0x80 {
            return 1;
        }

        // Check if it's in the GBK 2-byte table
        if gbk_encode_lookup(c).is_some() {
            return 2;
        }

        // Everything else is 4 bytes
        4
    }

    fn encode_char(c: char, buf: &mut [u8]) -> usize {
        let cp = c as u32;

        // ASCII
        if cp < 0x80 {
            buf[0] = cp as u8;
            return 1;
        }

        // Try 2-byte GBK
        if let Some(bytes) = gbk_encode_lookup(c) {
            buf[0] = (bytes >> 8) as u8;
            buf[1] = (bytes & 0xFF) as u8;
            return 2;
        }

        // 4-byte algorithmic encoding
        let (b1, b2, b3, b4) = encode_4byte(c);
        buf[0] = b1;
        buf[1] = b2;
        buf[2] = b3;
        buf[3] = b4;
        4
    }

    fn is_char_boundary(bytes: &[u8], index: usize) -> bool {
        if index == 0 || index >= bytes.len() {
            return index <= bytes.len();
        }

        let b = bytes[index];

        // ASCII is always a boundary
        if b < 0x80 {
            return true;
        }

        // Lead byte (0x81-0xFE) is a boundary
        if (0x81..=0xFE).contains(&b) {
            // But we need to check if the previous byte was a lead byte
            // that makes this a trail byte
            if index > 0 {
                let prev = bytes[index - 1];
                if (0x81..=0xFE).contains(&prev) {
                    // Previous is a lead byte, check if this could be a valid trail
                    if (0x40..=0x7E).contains(&b) || (0x80..=0xFE).contains(&b) {
                        return false; // This is a trail byte of a 2-byte sequence
                    }
                    if (0x30..=0x39).contains(&b) {
                        // Could be byte 2 of a 4-byte sequence, not a boundary
                        return false;
                    }
                }
            }
            return true;
        }

        // Trail bytes (0x30-0x39, 0x40-0x7E, 0x80) are not boundaries
        false
    }

    fn decode_char_before(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        if offset == 0 || offset > bytes.len() {
            return None;
        }

        // Try 1-byte (ASCII)
        let b1 = bytes[offset - 1];
        if b1 < 0x80 {
            return Some((b1 as char, offset - 1));
        }

        // Try 2-byte
        if offset >= 2 {
            let lead = bytes[offset - 2];
            let trail = bytes[offset - 1];
            if (0x81..=0xFE).contains(&lead) {
                if (0x40..=0x7E).contains(&trail) || (0x80..=0xFE).contains(&trail) {
                    if let Some(c) = decode_2byte(lead, trail) {
                        return Some((c, offset - 2));
                    }
                }
            }
        }

        // Try 4-byte
        if offset >= 4 {
            let b1 = bytes[offset - 4];
            let b2 = bytes[offset - 3];
            let b3 = bytes[offset - 2];
            let b4 = bytes[offset - 1];
            if (0x81..=0xFE).contains(&b1)
                && (0x30..=0x39).contains(&b2)
                && (0x81..=0xFE).contains(&b3)
                && (0x30..=0x39).contains(&b4)
            {
                if let Some(c) = decode_4byte(b1, b2, b3, b4) {
                    return Some((c, offset - 4));
                }
            }
        }

        None
    }
}

/// Decode a 2-byte GBK sequence.
fn decode_2byte(b1: u8, b2: u8) -> Option<char> {
    let key = ((b1 as u16) << 8) | (b2 as u16);
    // Binary search in the decode table
    GBK_DECODE_2BYTE
        .binary_search_by_key(&key, |&(k, _)| k)
        .ok()
        .map(|i| GBK_DECODE_2BYTE[i].1)
}

/// Look up 2-byte encoding for a character.
fn gbk_encode_lookup(c: char) -> Option<u16> {
    // Binary search in the encode table
    GBK_ENCODE
        .binary_search_by_key(&c, |&(ch, _)| ch)
        .ok()
        .map(|i| GBK_ENCODE[i].1)
}

/// Decode a 4-byte GB18030 sequence using the algorithmic mapping.
fn decode_4byte(b1: u8, b2: u8, b3: u8, b4: u8) -> Option<char> {
    // Validate byte ranges
    if !(0x81..=0xFE).contains(&b1) {
        return None;
    }
    if !(0x30..=0x39).contains(&b2) {
        return None;
    }
    if !(0x81..=0xFE).contains(&b3) {
        return None;
    }
    if !(0x30..=0x39).contains(&b4) {
        return None;
    }

    // Calculate linear index (pointer)
    let pointer = ((b1 as u32 - 0x81) * 12600)
        + ((b2 as u32 - 0x30) * 1260)
        + ((b3 as u32 - 0x81) * 10)
        + (b4 as u32 - 0x30);

    // Use the ranges table to find the codepoint
    pointer_to_codepoint(pointer)
}

/// Encode a character as 4-byte GB18030.
fn encode_4byte(c: char) -> (u8, u8, u8, u8) {
    let codepoint = c as u32;
    let pointer = codepoint_to_pointer(codepoint);

    let b4 = (pointer % 10) as u8 + 0x30;
    let pointer = pointer / 10;
    let b3 = (pointer % 126) as u8 + 0x81;
    let pointer = pointer / 126;
    let b2 = (pointer % 10) as u8 + 0x30;
    let b1 = (pointer / 10) as u8 + 0x81;

    (b1, b2, b3, b4)
}

/// Convert a 4-byte pointer to a Unicode codepoint using the ranges table.
fn pointer_to_codepoint(pointer: u32) -> Option<char> {
    // Binary search for the range containing this pointer
    let idx = match GB18030_RANGES.binary_search_by_key(&pointer, |&(p, _)| p) {
        Ok(i) => i,            // Exact match
        Err(0) => return None, // Before first range
        Err(i) => i - 1,       // In a range
    };

    let (range_pointer, range_codepoint) = GB18030_RANGES[idx];
    let offset = pointer - range_pointer;
    let codepoint = range_codepoint + offset;

    // Check we haven't gone past the next range
    if idx + 1 < GB18030_RANGES.len() {
        let (next_pointer, _) = GB18030_RANGES[idx + 1];
        if pointer >= next_pointer {
            return None;
        }
    }

    char::from_u32(codepoint)
}

/// Convert a Unicode codepoint to a 4-byte pointer using the ranges table.
fn codepoint_to_pointer(codepoint: u32) -> u32 {
    // Binary search for the range containing this codepoint
    let idx = match GB18030_RANGES.binary_search_by_key(&codepoint, |&(_, cp)| cp) {
        Ok(i) => i,
        Err(0) => 0,
        Err(i) => i - 1,
    };

    let (range_pointer, range_codepoint) = GB18030_RANGES[idx];
    let offset = codepoint - range_codepoint;
    range_pointer + offset
}

impl crate::encoding::UniversalEncoding for Gb18030 {}

// === Registry registration ===

#[cfg(feature = "registry")]
inventory::submit! {
    crate::registry::EncodingEntry {
        name: "GB18030",
        aliases: &["gb18030", "GB-18030", "gb-18030", "GBK", "gbk", "GB2312", "gb2312"],
        is_unicode: true,
        decode: |bytes| {
            Gb18030::validate(bytes)?;
            let mut chars = Vec::new();
            let mut offset = 0;
            while let Some((c, next)) = Gb18030::decode_char_at(bytes, offset) {
                chars.push(c);
                offset = next;
            }
            Ok(chars)
        },
        try_encode_char: |c| {
            let mut buf = [0u8; 4];
            let len = Gb18030::encode_char(c, &mut buf);
            Some(buf[..len].to_vec())
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ascii() {
        let mut buf = [0u8; 4];
        assert_eq!(Gb18030::encode_char('A', &mut buf), 1);
        assert_eq!(buf[0], b'A');

        let bytes = b"Hello";
        assert_eq!(Gb18030::decode_char_at(bytes, 0), Some(('H', 1)));
    }

    #[test]
    fn test_2byte_gbk() {
        // Test a common Chinese character: 中 (U+4E2D)
        // In GBK, 中 is encoded as 0xD6D0
        let mut buf = [0u8; 4];
        let len = Gb18030::encode_char('中', &mut buf);
        assert_eq!(len, 2);
        assert_eq!(buf[0], 0xD6);
        assert_eq!(buf[1], 0xD0);

        // Decode it back
        assert_eq!(Gb18030::decode_char_at(&[0xD6, 0xD0], 0), Some(('中', 2)));
    }

    #[test]
    fn test_4byte() {
        // Test a character not in GBK that requires 4-byte encoding
        // U+20000 (𠀀) - first CJK Extension B character
        let mut buf = [0u8; 4];
        let len = Gb18030::encode_char('\u{20000}', &mut buf);
        assert_eq!(len, 4);

        // Decode it back
        let decoded = Gb18030::decode_char_at(&buf, 0);
        assert_eq!(decoded, Some(('\u{20000}', 4)));
    }

    #[test]
    fn test_euro_sign() {
        // Euro sign € (U+20AC) is in the 4-byte range for GB18030
        // (it's not in GBK)
        let mut buf = [0u8; 4];
        let len = Gb18030::encode_char('€', &mut buf);

        // Decode it back
        let decoded = Gb18030::decode_char_at(&buf[..len], 0);
        assert_eq!(decoded.map(|(c, _)| c), Some('€'));
    }

    #[test]
    fn test_validate() {
        // Valid ASCII
        assert!(Gb18030::validate(b"Hello").is_ok());

        // Valid 2-byte
        assert!(Gb18030::validate(&[0xD6, 0xD0]).is_ok());

        // Invalid: truncated 2-byte
        assert!(Gb18030::validate(&[0xD6]).is_err());

        // Invalid: bad trail byte
        assert!(Gb18030::validate(&[0xD6, 0x20]).is_err());
    }

    #[test]
    fn test_roundtrip() {
        // Test roundtrip for various characters
        let chars = ['A', '中', '国', '€', '\u{20000}', '日', '本'];
        for c in chars {
            let mut buf = [0u8; 4];
            let len = Gb18030::encode_char(c, &mut buf);
            let decoded = Gb18030::decode_char_at(&buf[..len], 0);
            assert_eq!(decoded, Some((c, len)), "Failed roundtrip for {:?}", c);
        }
    }
}
