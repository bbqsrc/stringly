//! EUC-KR encoding.
//!
//! EUC-KR (Extended Unix Code for Korean) is a variable-width encoding used
//! for Korean text. It is compatible with the KS X 1001 standard and is widely
//! used in Korea.
//!
//! # Structure
//!
//! EUC-KR uses variable-width encoding:
//! - 1 byte: ASCII (0x00-0x7F)
//! - 2 bytes: Korean characters (lead 0x81-0xFE, trail 0x41-0xFE)
//!
//! The WHATWG variant (used here) is compatible with Windows code page 949,
//! which extends EUC-KR with additional Hangul syllables.

use alloc::vec::Vec;

use crate::encoding::Encoding;
use crate::error::EncodingError;

// Include generated tables
include!(concat!(env!("OUT_DIR"), "/euckr_tables.rs"));

/// EUC-KR encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct EucKr;

/// Look up a character by pointer in the decode table.
fn euckr_lookup(pointer: u16) -> Option<char> {
    EUCKR_DECODE
        .binary_search_by_key(&pointer, |&(p, _)| p)
        .ok()
        .map(|idx| EUCKR_DECODE[idx].1)
}

/// Look up a pointer by character in the encode table.
fn euckr_encode_lookup(c: char) -> Option<u16> {
    EUCKR_ENCODE
        .binary_search_by_key(&c, |&(ch, _)| ch)
        .ok()
        .map(|idx| EUCKR_ENCODE[idx].1)
}

impl Encoding for EucKr {
    const NAME: &'static str = "EUC-KR";
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
                if !((0x41..=0x5A).contains(&b2)
                    || (0x61..=0x7A).contains(&b2)
                    || (0x81..=0xFE).contains(&b2))
                {
                    return Err(EncodingError::new(i, Some(2)));
                }
                // Validate the sequence maps to a valid character
                let pointer = pointer_from_bytes(b1, b2);
                if euckr_lookup(pointer).is_none() {
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
            let pointer = pointer_from_bytes(b1, b2);
            let c = euckr_lookup(pointer)?;
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
        if let Some(pointer) = euckr_encode_lookup(c) {
            let (b1, b2) = bytes_from_pointer(pointer);
            buf[0] = b1;
            buf[1] = b2;
            return 2;
        }

        panic!("character '{}' cannot be encoded in EUC-KR", c);
    }

    fn try_encode_char(c: char, buf: &mut [u8]) -> Option<usize> {
        let cp = c as u32;

        // ASCII
        if cp < 0x80 {
            buf[0] = cp as u8;
            return Some(1);
        }

        // Look up in encode table
        let pointer = euckr_encode_lookup(c)?;
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
        euckr_encode_lookup(c).is_some()
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
            } else if (0x81..=0xFE).contains(&b) && pos + 1 < bytes.len() {
                let b2 = bytes[pos + 1];
                if (0x41..=0x5A).contains(&b2)
                    || (0x61..=0x7A).contains(&b2)
                    || (0x81..=0xFE).contains(&b2)
                {
                    // Valid 2-byte sequence
                    pos += 2;
                } else {
                    // Invalid trail byte - treat as single byte boundary
                    pos += 1;
                }
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
        if offset >= 2 {
            let b1 = bytes[offset - 2];
            let b2 = b;
            if (0x81..=0xFE).contains(&b1) {
                let pointer = pointer_from_bytes(b1, b2);
                if let Some(c) = euckr_lookup(pointer) {
                    return Some((c, offset - 2));
                }
            }
        }

        None
    }
}

/// Convert lead and trail bytes to a WHATWG pointer.
///
/// WHATWG EUC-KR pointer formula:
/// pointer = (lead - 0x81) * 190 + (trail - 0x41)
#[inline]
fn pointer_from_bytes(lead: u8, trail: u8) -> u16 {
    ((lead - 0x81) as u16) * 190 + (trail - 0x41) as u16
}

/// Convert a WHATWG pointer back to lead and trail bytes.
#[inline]
fn bytes_from_pointer(pointer: u16) -> (u8, u8) {
    let lead = (pointer / 190) as u8 + 0x81;
    let trail = (pointer % 190) as u8 + 0x41;
    (lead, trail)
}

impl crate::encoding::LimitedEncoding for EucKr {}

#[cfg(feature = "registry")]
inventory::submit! {
    crate::registry::EncodingEntry {
        name: "EUC-KR",
        aliases: &["euc-kr", "euckr", "EUC_KR", "cp949", "CP949", "Windows-949", "windows-949"],
        is_unicode: false,
        decode: |bytes| {
            EucKr::validate(bytes)?;
            let mut chars = Vec::new();
            let mut offset = 0;
            while let Some((c, next)) = EucKr::decode_char_at(bytes, offset) {
                chars.push(c);
                offset = next;
            }
            Ok(chars)
        },
        try_encode_char: |c| {
            let mut buf = [0u8; 2];
            EucKr::try_encode_char(c, &mut buf).map(|len| buf[..len].to_vec())
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ascii() {
        let bytes = b"Hello";
        assert!(EucKr::validate(bytes).is_ok());

        let (c, next) = EucKr::decode_char_at(bytes, 0).unwrap();
        assert_eq!(c, 'H');
        assert_eq!(next, 1);
    }

    #[test]
    fn test_korean() {
        // 가 (U+AC00) - first Hangul syllable
        // In EUC-KR: 0xB0A1
        let mut buf = [0u8; 2];
        let len = EucKr::encode_char('가', &mut buf);
        assert_eq!(len, 2);

        let (c, _) = EucKr::decode_char_at(&buf, 0).unwrap();
        assert_eq!(c, '가');
    }

    #[test]
    fn test_roundtrip() {
        let test_chars = ['A', '가', '나', '다', '한', '글'];
        for &c in &test_chars {
            if EucKr::can_encode(c) {
                let mut buf = [0u8; 4];
                let len = EucKr::encode_char(c, &mut buf);
                let (decoded, _) = EucKr::decode_char_at(&buf[..len], 0).unwrap();
                assert_eq!(c, decoded, "Roundtrip failed for '{}'", c);
            }
        }
    }

    #[test]
    fn test_validate() {
        // Valid ASCII
        assert!(EucKr::validate(b"Hello").is_ok());

        // Invalid: lone lead byte
        assert!(EucKr::validate(&[0x81]).is_err());

        // Invalid: bad trail byte
        assert!(EucKr::validate(&[0x81, 0x20]).is_err());
    }

    #[test]
    fn test_is_char_boundary() {
        // 가나 in EUC-KR
        let s: crate::String<EucKr> = "가나".chars().collect();
        let bytes = s.as_bytes();

        assert!(EucKr::is_char_boundary(bytes, 0));
        assert!(!EucKr::is_char_boundary(bytes, 1));
        assert!(EucKr::is_char_boundary(bytes, 2));
        assert!(!EucKr::is_char_boundary(bytes, 3));
        assert!(EucKr::is_char_boundary(bytes, 4));
    }

    #[test]
    fn test_decode_char_before() {
        let s: crate::String<EucKr> = "A가B".chars().collect();
        let bytes = s.as_bytes();

        // From end
        let (c, pos) = EucKr::decode_char_before(bytes, bytes.len()).unwrap();
        assert_eq!(c, 'B');

        let (c, pos) = EucKr::decode_char_before(bytes, pos).unwrap();
        assert_eq!(c, '가');

        let (c, _) = EucKr::decode_char_before(bytes, pos).unwrap();
        assert_eq!(c, 'A');
    }
}
