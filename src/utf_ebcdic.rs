//! UTF-EBCDIC encoding implementation.
//!
//! UTF-EBCDIC (Unicode Technical Report #16) is a transformation format that maps Unicode
//! to byte sequences compatible with EBCDIC systems (IBM mainframes).
//!
//! # Overview
//!
//! UTF-EBCDIC is conceptually similar to UTF-8 but uses byte values that work well
//! with EBCDIC-based systems:
//!
//! - Single-byte characters use EBCDIC control codes and basic Latin
//! - Multi-byte sequences use continuation bytes in EBCDIC-compatible ranges
//! - Variable-length encoding: 1-4 bytes for BMP, 5 bytes for supplementary
//!
//! # Algorithm
//!
//! The encoding works by:
//! 1. Converting the codepoint to an "Intermediate-8" (I8) representation (similar to UTF-8)
//! 2. Permuting each I8 byte through a mapping table to get EBCDIC-friendly bytes
//!
//! # Use Cases
//!
//! UTF-EBCDIC is primarily used on IBM mainframe systems (z/OS, OS/400) where native
//! character encoding is EBCDIC rather than ASCII.

use alloc::vec::Vec;

use crate::encoding::{Encoding, UniversalEncoding};
use crate::error::EncodingError;

/// UTF-EBCDIC encoding marker.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct UtfEbcdic;

// Intermediate-8 (I8) to EBCDIC permutation table
// This maps the UTF-8-like intermediate bytes to EBCDIC-compatible values
// Based on Unicode Technical Report #16
#[rustfmt::skip]
const I8_TO_EBCDIC: [u8; 256] = [
    // 0x00-0x0F: Control characters (mapped to EBCDIC controls)
    0x00, 0x01, 0x02, 0x03, 0x37, 0x2D, 0x2E, 0x2F,
    0x16, 0x05, 0x25, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
    // 0x10-0x1F
    0x10, 0x11, 0x12, 0x13, 0x3C, 0x3D, 0x32, 0x26,
    0x18, 0x19, 0x3F, 0x27, 0x1C, 0x1D, 0x1E, 0x1F,
    // 0x20-0x2F: Punctuation and special
    0x40, 0x5A, 0x7F, 0x7B, 0x5B, 0x6C, 0x50, 0x7D,
    0x4D, 0x5D, 0x5C, 0x4E, 0x6B, 0x60, 0x4B, 0x61,
    // 0x30-0x3F: Digits
    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6, 0xF7,
    0xF8, 0xF9, 0x7A, 0x5E, 0x4C, 0x7E, 0x6E, 0x6F,
    // 0x40-0x4F: Uppercase A-O
    0x7C, 0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7,
    0xC8, 0xC9, 0xD1, 0xD2, 0xD3, 0xD4, 0xD5, 0xD6,
    // 0x50-0x5F: Uppercase P-Z and special
    0xD7, 0xD8, 0xD9, 0xE2, 0xE3, 0xE4, 0xE5, 0xE6,
    0xE7, 0xE8, 0xE9, 0xBA, 0xB8, 0xBB, 0xB0, 0x6D,
    // 0x60-0x6F: Lowercase a-o
    0x79, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87,
    0x88, 0x89, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96,
    // 0x70-0x7F: Lowercase p-z and special
    0x97, 0x98, 0x99, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6,
    0xA7, 0xA8, 0xA9, 0xC0, 0x4F, 0xD0, 0xA1, 0x07,
    // 0x80-0x9F: Continuation bytes in I8 -> EBCDIC continuation byte range
    0x20, 0x21, 0x22, 0x23, 0x24, 0x15, 0x06, 0x17,
    0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x09, 0x0A, 0x1B,
    0x30, 0x31, 0x1A, 0x33, 0x34, 0x35, 0x36, 0x08,
    0x38, 0x39, 0x3A, 0x3B, 0x04, 0x14, 0x3E, 0xFF,
    // 0xA0-0xBF: More continuation bytes
    0x41, 0xAA, 0x4A, 0xB1, 0x9F, 0xB2, 0x6A, 0xB5,
    0xBD, 0xB4, 0x9A, 0x8A, 0x5F, 0xCA, 0xAF, 0xBC,
    0x90, 0x8F, 0xEA, 0xFA, 0xBE, 0xA0, 0xB6, 0xB3,
    0x9D, 0xDA, 0x9B, 0x8B, 0xB7, 0xB8, 0xB9, 0xAB,
    // 0xC0-0xDF: Lead bytes for 2-byte sequences
    0x64, 0x65, 0x62, 0x66, 0x63, 0x67, 0x9E, 0x68,
    0x74, 0x71, 0x72, 0x73, 0x78, 0x75, 0x76, 0x77,
    0xAC, 0x69, 0xED, 0xEE, 0xEB, 0xEF, 0xEC, 0xBF,
    0x80, 0xFD, 0xFE, 0xFB, 0xFC, 0xAD, 0xAE, 0x59,
    // 0xE0-0xEF: Lead bytes for 3-byte sequences
    0x44, 0x45, 0x42, 0x46, 0x43, 0x47, 0x9C, 0x48,
    0x54, 0x51, 0x52, 0x53, 0x58, 0x55, 0x56, 0x57,
    // 0xF0-0xF7: Lead bytes for 4-byte sequences
    0x8C, 0x49, 0xCD, 0xCE, 0xCB, 0xCF, 0xCC, 0xE1,
    // 0xF8-0xFB: Lead bytes for 5-byte sequences
    0x70, 0xDD, 0xDE, 0xDB,
    // 0xFC-0xFF: Reserved/invalid
    0xDC, 0x8D, 0x8E, 0xDF,
];

// EBCDIC to Intermediate-8 (I8) reverse permutation table
#[rustfmt::skip]
const EBCDIC_TO_I8: [u8; 256] = {
    let mut table = [0u8; 256];
    let mut i = 0;
    while i < 256 {
        table[I8_TO_EBCDIC[i] as usize] = i as u8;
        i += 1;
    }
    table
};

impl Encoding for UtfEbcdic {
    const NAME: &'static str = "UTF-EBCDIC";
    const IS_FIXED_WIDTH: bool = false;
    const BYTES_PER_CHAR: Option<usize> = None;
    const MAX_CHAR_LEN: usize = 5; // Supplementary characters need 5 bytes

    fn validate(bytes: &[u8]) -> Result<(), EncodingError> {
        let mut i = 0;
        while i < bytes.len() {
            let i8_byte = EBCDIC_TO_I8[bytes[i] as usize];
            let len = i8_char_len(i8_byte);

            if len == 0 {
                return Err(EncodingError::new(i, Some(1)));
            }

            if i + len > bytes.len() {
                return Err(EncodingError::new(i, Some(bytes.len() - i)));
            }

            // Validate continuation bytes
            for j in 1..len {
                let cont_i8 = EBCDIC_TO_I8[bytes[i + j] as usize];
                if !is_i8_continuation(cont_i8) {
                    return Err(EncodingError::new(i + j, Some(1)));
                }
            }

            // Decode and validate the codepoint
            if let Some(cp) = decode_i8_sequence(&bytes[i..i + len]) {
                if cp > 0x10FFFF {
                    return Err(EncodingError::new(i, Some(len)));
                }
                // Check for overlong encoding
                let expected_len = codepoint_to_i8_len(cp);
                if len != expected_len {
                    return Err(EncodingError::new(i, Some(len)));
                }
            } else {
                return Err(EncodingError::new(i, Some(len)));
            }

            i += len;
        }
        Ok(())
    }

    fn decode_char_at(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        if offset >= bytes.len() {
            return None;
        }

        let i8_byte = EBCDIC_TO_I8[bytes[offset] as usize];
        let len = i8_char_len(i8_byte);

        if len == 0 || offset + len > bytes.len() {
            return None;
        }

        let cp = decode_i8_sequence(&bytes[offset..offset + len])?;
        char::from_u32(cp).map(|c| (c, offset + len))
    }

    fn encoded_len(c: char) -> usize {
        codepoint_to_i8_len(c as u32)
    }

    fn encode_char(c: char, buf: &mut [u8]) -> usize {
        let cp = c as u32;
        let len = codepoint_to_i8_len(cp);

        // Encode to I8 first, then permute to EBCDIC
        match len {
            1 => {
                buf[0] = I8_TO_EBCDIC[cp as usize];
            }
            2 => {
                let i8_bytes = [0xC0 | ((cp >> 6) as u8 & 0x1F), 0x80 | (cp as u8 & 0x3F)];
                buf[0] = I8_TO_EBCDIC[i8_bytes[0] as usize];
                buf[1] = I8_TO_EBCDIC[i8_bytes[1] as usize];
            }
            3 => {
                let i8_bytes = [
                    0xE0 | ((cp >> 12) as u8 & 0x0F),
                    0x80 | ((cp >> 6) as u8 & 0x3F),
                    0x80 | (cp as u8 & 0x3F),
                ];
                buf[0] = I8_TO_EBCDIC[i8_bytes[0] as usize];
                buf[1] = I8_TO_EBCDIC[i8_bytes[1] as usize];
                buf[2] = I8_TO_EBCDIC[i8_bytes[2] as usize];
            }
            4 => {
                let i8_bytes = [
                    0xF0 | ((cp >> 18) as u8 & 0x07),
                    0x80 | ((cp >> 12) as u8 & 0x3F),
                    0x80 | ((cp >> 6) as u8 & 0x3F),
                    0x80 | (cp as u8 & 0x3F),
                ];
                buf[0] = I8_TO_EBCDIC[i8_bytes[0] as usize];
                buf[1] = I8_TO_EBCDIC[i8_bytes[1] as usize];
                buf[2] = I8_TO_EBCDIC[i8_bytes[2] as usize];
                buf[3] = I8_TO_EBCDIC[i8_bytes[3] as usize];
            }
            5 => {
                // For codepoints > U+FFFF in 5-byte encoding
                let i8_bytes = [
                    0xF8 | ((cp >> 24) as u8 & 0x03),
                    0x80 | ((cp >> 18) as u8 & 0x3F),
                    0x80 | ((cp >> 12) as u8 & 0x3F),
                    0x80 | ((cp >> 6) as u8 & 0x3F),
                    0x80 | (cp as u8 & 0x3F),
                ];
                buf[0] = I8_TO_EBCDIC[i8_bytes[0] as usize];
                buf[1] = I8_TO_EBCDIC[i8_bytes[1] as usize];
                buf[2] = I8_TO_EBCDIC[i8_bytes[2] as usize];
                buf[3] = I8_TO_EBCDIC[i8_bytes[3] as usize];
                buf[4] = I8_TO_EBCDIC[i8_bytes[4] as usize];
            }
            _ => unreachable!(),
        }

        len
    }

    fn is_char_boundary(bytes: &[u8], index: usize) -> bool {
        if index == 0 || index >= bytes.len() {
            return index <= bytes.len();
        }

        // Convert to I8 and check if it's a continuation byte
        let i8_byte = EBCDIC_TO_I8[bytes[index] as usize];
        !is_i8_continuation(i8_byte)
    }

    fn decode_char_before(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        if offset == 0 || offset > bytes.len() {
            return None;
        }

        // Scan backwards to find the start of the character
        let mut start = offset - 1;
        while start > 0 {
            let i8_byte = EBCDIC_TO_I8[bytes[start] as usize];
            if !is_i8_continuation(i8_byte) {
                break;
            }
            start -= 1;
        }

        // Decode and verify
        let (c, end) = Self::decode_char_at(bytes, start)?;
        if end == offset {
            Some((c, start))
        } else {
            None
        }
    }
}

impl UniversalEncoding for UtfEbcdic {}

/// Returns the character length based on the I8 lead byte.
fn i8_char_len(i8_byte: u8) -> usize {
    if i8_byte < 0x80 {
        1 // ASCII/single byte
    } else if i8_byte < 0xC0 {
        0 // Continuation byte (invalid as lead)
    } else if i8_byte < 0xE0 {
        2
    } else if i8_byte < 0xF0 {
        3
    } else if i8_byte < 0xF8 {
        4
    } else if i8_byte < 0xFC {
        5
    } else {
        0 // Invalid
    }
}

/// Returns true if the I8 byte is a continuation byte.
#[inline]
fn is_i8_continuation(i8_byte: u8) -> bool {
    (i8_byte & 0xC0) == 0x80
}

/// Calculate the I8 encoding length for a codepoint.
fn codepoint_to_i8_len(cp: u32) -> usize {
    if cp < 0x80 {
        1
    } else if cp < 0x800 {
        2
    } else if cp < 0x10000 {
        3
    } else if cp < 0x200000 {
        4
    } else {
        5
    }
}

/// Decode an EBCDIC byte sequence to a Unicode codepoint.
fn decode_i8_sequence(ebcdic_bytes: &[u8]) -> Option<u32> {
    if ebcdic_bytes.is_empty() {
        return None;
    }

    // Convert EBCDIC bytes to I8 bytes
    let i8_lead = EBCDIC_TO_I8[ebcdic_bytes[0] as usize];
    let len = i8_char_len(i8_lead);

    if len == 0 || len != ebcdic_bytes.len() {
        return None;
    }

    match len {
        1 => Some(i8_lead as u32),
        2 => {
            let i8_1 = EBCDIC_TO_I8[ebcdic_bytes[1] as usize];
            if !is_i8_continuation(i8_1) {
                return None;
            }
            Some(((i8_lead as u32 & 0x1F) << 6) | (i8_1 as u32 & 0x3F))
        }
        3 => {
            let i8_1 = EBCDIC_TO_I8[ebcdic_bytes[1] as usize];
            let i8_2 = EBCDIC_TO_I8[ebcdic_bytes[2] as usize];
            if !is_i8_continuation(i8_1) || !is_i8_continuation(i8_2) {
                return None;
            }
            Some(
                ((i8_lead as u32 & 0x0F) << 12)
                    | ((i8_1 as u32 & 0x3F) << 6)
                    | (i8_2 as u32 & 0x3F),
            )
        }
        4 => {
            let i8_1 = EBCDIC_TO_I8[ebcdic_bytes[1] as usize];
            let i8_2 = EBCDIC_TO_I8[ebcdic_bytes[2] as usize];
            let i8_3 = EBCDIC_TO_I8[ebcdic_bytes[3] as usize];
            if !is_i8_continuation(i8_1) || !is_i8_continuation(i8_2) || !is_i8_continuation(i8_3) {
                return None;
            }
            Some(
                ((i8_lead as u32 & 0x07) << 18)
                    | ((i8_1 as u32 & 0x3F) << 12)
                    | ((i8_2 as u32 & 0x3F) << 6)
                    | (i8_3 as u32 & 0x3F),
            )
        }
        5 => {
            let i8_1 = EBCDIC_TO_I8[ebcdic_bytes[1] as usize];
            let i8_2 = EBCDIC_TO_I8[ebcdic_bytes[2] as usize];
            let i8_3 = EBCDIC_TO_I8[ebcdic_bytes[3] as usize];
            let i8_4 = EBCDIC_TO_I8[ebcdic_bytes[4] as usize];
            if !is_i8_continuation(i8_1)
                || !is_i8_continuation(i8_2)
                || !is_i8_continuation(i8_3)
                || !is_i8_continuation(i8_4)
            {
                return None;
            }
            Some(
                ((i8_lead as u32 & 0x03) << 24)
                    | ((i8_1 as u32 & 0x3F) << 18)
                    | ((i8_2 as u32 & 0x3F) << 12)
                    | ((i8_3 as u32 & 0x3F) << 6)
                    | (i8_4 as u32 & 0x3F),
            )
        }
        _ => None,
    }
}

#[cfg(feature = "registry")]
inventory::submit! {
    crate::registry::EncodingEntry {
        name: "UTF-EBCDIC",
        aliases: &["UTFEBCDIC", "utf-ebcdic", "utfebcdic"],
        is_unicode: true,
        decode: |bytes| {
            UtfEbcdic::validate(bytes)?;
            let mut result = Vec::new();
            let mut offset = 0;
            while let Some((c, next)) = UtfEbcdic::decode_char_at(bytes, offset) {
                result.push(c);
                offset = next;
            }
            Ok(result)
        },
        try_encode_char: |c| {
            let mut buf = [0u8; 5];
            let len = UtfEbcdic::encode_char(c, &mut buf);
            Some(buf[..len].to_vec())
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ascii_roundtrip() {
        // Test basic ASCII characters
        for c in b'A'..=b'Z' {
            let mut buf = [0u8; 5];
            let len = UtfEbcdic::encode_char(c as char, &mut buf);
            assert_eq!(len, 1);

            assert!(UtfEbcdic::validate(&buf[..len]).is_ok());
            let (decoded, _) = UtfEbcdic::decode_char_at(&buf[..len], 0).unwrap();
            assert_eq!(decoded, c as char);
        }
    }

    #[test]
    fn test_digits() {
        for c in b'0'..=b'9' {
            let mut buf = [0u8; 5];
            let len = UtfEbcdic::encode_char(c as char, &mut buf);

            let (decoded, _) = UtfEbcdic::decode_char_at(&buf[..len], 0).unwrap();
            assert_eq!(decoded, c as char);
        }
    }

    #[test]
    fn test_multibyte() {
        // é is U+00E9 (needs 2 bytes)
        let mut buf = [0u8; 5];
        let len = UtfEbcdic::encode_char('é', &mut buf);
        assert_eq!(len, 2);

        assert!(UtfEbcdic::validate(&buf[..len]).is_ok());
        let (decoded, _) = UtfEbcdic::decode_char_at(&buf[..len], 0).unwrap();
        assert_eq!(decoded, 'é');
    }

    #[test]
    fn test_cjk() {
        // 日 is U+65E5 (needs 3 bytes)
        let mut buf = [0u8; 5];
        let len = UtfEbcdic::encode_char('日', &mut buf);
        assert_eq!(len, 3);

        assert!(UtfEbcdic::validate(&buf[..len]).is_ok());
        let (decoded, _) = UtfEbcdic::decode_char_at(&buf[..len], 0).unwrap();
        assert_eq!(decoded, '日');
    }

    #[test]
    fn test_supplementary() {
        // 😀 is U+1F600 (needs 4 bytes in UTF-8, but UTF-EBCDIC may differ)
        let mut buf = [0u8; 5];
        let len = UtfEbcdic::encode_char('😀', &mut buf);

        assert!(UtfEbcdic::validate(&buf[..len]).is_ok());
        let (decoded, _) = UtfEbcdic::decode_char_at(&buf[..len], 0).unwrap();
        assert_eq!(decoded, '😀');
    }

    #[test]
    fn test_encoded_len() {
        assert_eq!(UtfEbcdic::encoded_len('A'), 1);
        assert_eq!(UtfEbcdic::encoded_len('é'), 2);
        assert_eq!(UtfEbcdic::encoded_len('日'), 3);
        assert_eq!(UtfEbcdic::encoded_len('😀'), 4);
    }

    #[test]
    fn test_is_char_boundary() {
        let mut buf = [0u8; 5];
        let len = UtfEbcdic::encode_char('日', &mut buf);

        assert!(UtfEbcdic::is_char_boundary(&buf[..len], 0));
        assert!(!UtfEbcdic::is_char_boundary(&buf[..len], 1));
        assert!(!UtfEbcdic::is_char_boundary(&buf[..len], 2));
    }

    #[test]
    fn test_string_roundtrip() {
        let test_str = "Hello, 世界! 😀";
        let mut encoded = Vec::new();

        for c in test_str.chars() {
            let mut buf = [0u8; 5];
            let len = UtfEbcdic::encode_char(c, &mut buf);
            encoded.extend_from_slice(&buf[..len]);
        }

        assert!(UtfEbcdic::validate(&encoded).is_ok());

        let mut decoded = alloc::string::String::new();
        let mut offset = 0;
        while let Some((c, next)) = UtfEbcdic::decode_char_at(&encoded, offset) {
            decoded.push(c);
            offset = next;
        }

        assert_eq!(decoded, test_str);
    }
}
