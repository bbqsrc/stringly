//! EUC-JP encoding.
//!
//! EUC-JP (Extended Unix Code for Japanese) is a variable-width encoding used
//! primarily on Unix systems in Japan. It can represent ASCII, JIS X 0201
//! half-width katakana, JIS X 0208 (common Japanese characters), and JIS X 0212
//! (supplementary characters).
//!
//! # Structure
//!
//! EUC-JP uses variable-width encoding:
//! - 1 byte: ASCII (0x00-0x7F)
//! - 2 bytes: JIS X 0201 Katakana (0x8E + 0xA1-0xDF)
//! - 2 bytes: JIS X 0208 (0xA1-0xFE + 0xA1-0xFE)
//! - 3 bytes: JIS X 0212 (0x8F + 0xA1-0xFE + 0xA1-0xFE)

use alloc::vec::Vec;

use crate::encoding::Encoding;
use crate::error::EncodingError;

// Include generated tables
include!(concat!(env!("OUT_DIR"), "/jis0208_tables.rs"));
include!(concat!(env!("OUT_DIR"), "/jis0212_tables.rs"));

/// EUC-JP encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct EucJp;

impl Encoding for EucJp {
    const NAME: &'static str = "EUC-JP";
    const IS_FIXED_WIDTH: bool = false;
    const BYTES_PER_CHAR: Option<usize> = None;
    const MAX_CHAR_LEN: usize = 3;

    fn validate(bytes: &[u8]) -> Result<(), EncodingError> {
        let mut i = 0;
        while i < bytes.len() {
            let b1 = bytes[i];

            if b1 < 0x80 {
                // ASCII
                i += 1;
            } else if b1 == 0x8E {
                // JIS X 0201 Katakana (2 bytes)
                if i + 1 >= bytes.len() {
                    return Err(EncodingError::new(i, Some(1)));
                }
                let b2 = bytes[i + 1];
                if !(0xA1..=0xDF).contains(&b2) {
                    return Err(EncodingError::new(i, Some(2)));
                }
                i += 2;
            } else if b1 == 0x8F {
                // JIS X 0212 (3 bytes)
                if i + 2 >= bytes.len() {
                    return Err(EncodingError::new(i, Some(bytes.len() - i)));
                }
                let b2 = bytes[i + 1];
                let b3 = bytes[i + 2];
                if !(0xA1..=0xFE).contains(&b2) || !(0xA1..=0xFE).contains(&b3) {
                    return Err(EncodingError::new(i, Some(3)));
                }
                // Validate the sequence maps to a valid character
                let pointer = ((b2 - 0xA1) as u16) * 94 + (b3 - 0xA1) as u16;
                if jis0212_lookup(pointer).is_none() {
                    return Err(EncodingError::new(i, Some(3)));
                }
                i += 3;
            } else if (0xA1..=0xFE).contains(&b1) {
                // JIS X 0208 (2 bytes)
                if i + 1 >= bytes.len() {
                    return Err(EncodingError::new(i, Some(1)));
                }
                let b2 = bytes[i + 1];
                if !(0xA1..=0xFE).contains(&b2) {
                    return Err(EncodingError::new(i, Some(2)));
                }
                // Validate the sequence maps to a valid character
                let pointer = ((b1 - 0xA1) as u16) * 94 + (b2 - 0xA1) as u16;
                if jis0208_lookup(pointer).is_none() {
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

        // JIS X 0201 Katakana: 0x8E + 0xA1-0xDF
        if b1 == 0x8E {
            let b2 = *bytes.get(offset + 1)?;
            if (0xA1..=0xDF).contains(&b2) {
                // Map to U+FF61-U+FF9F (half-width katakana)
                let c = char::from_u32(0xFF61 + (b2 - 0xA1) as u32)?;
                return Some((c, offset + 2));
            }
            return None;
        }

        // JIS X 0212: 0x8F + 0xA1-0xFE + 0xA1-0xFE
        if b1 == 0x8F {
            let b2 = *bytes.get(offset + 1)?;
            let b3 = *bytes.get(offset + 2)?;
            if (0xA1..=0xFE).contains(&b2) && (0xA1..=0xFE).contains(&b3) {
                let pointer = ((b2 - 0xA1) as u16) * 94 + (b3 - 0xA1) as u16;
                let c = jis0212_lookup(pointer)?;
                return Some((c, offset + 3));
            }
            return None;
        }

        // JIS X 0208: 0xA1-0xFE + 0xA1-0xFE
        if (0xA1..=0xFE).contains(&b1) {
            let b2 = *bytes.get(offset + 1)?;
            if (0xA1..=0xFE).contains(&b2) {
                let pointer = ((b1 - 0xA1) as u16) * 94 + (b2 - 0xA1) as u16;
                let c = jis0208_lookup(pointer)?;
                return Some((c, offset + 2));
            }
            return None;
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
            return 2;
        }

        // Check if it's in JIS X 0208
        if jis0208_encode_lookup(c).is_some() {
            return 2;
        }

        // JIS X 0212 would be 3 bytes, but we don't encode to it
        // Characters not in the encoding can't be encoded
        2 // Will fail in encode_char
    }

    fn encode_char(c: char, buf: &mut [u8]) -> usize {
        let cp = c as u32;

        // ASCII
        if cp < 0x80 {
            buf[0] = cp as u8;
            return 1;
        }

        // Half-width katakana (U+FF61-U+FF9F) -> 0x8E + 0xA1-0xDF
        if (0xFF61..=0xFF9F).contains(&cp) {
            buf[0] = 0x8E;
            buf[1] = (cp - 0xFF61 + 0xA1) as u8;
            return 2;
        }

        // JIS X 0208
        if let Some(pointer) = jis0208_encode_lookup(c) {
            let row = pointer / 94;
            let col = pointer % 94;
            buf[0] = (row + 0xA1) as u8;
            buf[1] = (col + 0xA1) as u8;
            return 2;
        }

        panic!(
            "character '{}' (U+{:04X}) cannot be encoded in EUC-JP",
            c, cp
        );
    }

    fn try_encode_char(c: char, buf: &mut [u8]) -> Option<usize> {
        let cp = c as u32;

        // ASCII
        if cp < 0x80 {
            buf[0] = cp as u8;
            return Some(1);
        }

        // Half-width katakana (U+FF61-U+FF9F) -> 0x8E + 0xA1-0xDF
        if (0xFF61..=0xFF9F).contains(&cp) {
            buf[0] = 0x8E;
            buf[1] = (cp - 0xFF61 + 0xA1) as u8;
            return Some(2);
        }

        // JIS X 0208
        if let Some(pointer) = jis0208_encode_lookup(c) {
            let row = pointer / 94;
            let col = pointer % 94;
            buf[0] = (row + 0xA1) as u8;
            buf[1] = (col + 0xA1) as u8;
            return Some(2);
        }

        None
    }

    fn can_encode(c: char) -> bool {
        let cp = c as u32;

        // ASCII
        if cp < 0x80 {
            return true;
        }

        // Half-width katakana
        if (0xFF61..=0xFF9F).contains(&cp) {
            return true;
        }

        // JIS X 0208
        jis0208_encode_lookup(c).is_some()
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

        // Lead bytes (0x8E, 0x8F, 0xA1-0xFE) are boundaries
        // But we need to check if the previous byte makes this a trail byte
        if index > 0 {
            let prev = bytes[index - 1];

            // After 0x8E (JIS X 0201 prefix), we're in a trail byte
            if prev == 0x8E {
                return false;
            }

            // After 0x8F (JIS X 0212 prefix), we're in a trail byte
            if prev == 0x8F {
                return false;
            }

            // After 0xA1-0xFE (JIS X 0208 lead), if current is 0xA1-0xFE, it's a trail
            if (0xA1..=0xFE).contains(&prev) && (0xA1..=0xFE).contains(&b) {
                return false;
            }

            // Check for second byte of 3-byte JIS X 0212 sequence
            if index >= 2 && bytes[index - 2] == 0x8F {
                return false;
            }
        }

        true
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

        // Try 2-byte JIS X 0201 Katakana
        if offset >= 2 {
            let lead = bytes[offset - 2];
            let trail = bytes[offset - 1];
            if lead == 0x8E && (0xA1..=0xDF).contains(&trail) {
                let c = char::from_u32(0xFF61 + (trail - 0xA1) as u32)?;
                return Some((c, offset - 2));
            }
        }

        // Try 2-byte JIS X 0208
        if offset >= 2 {
            let lead = bytes[offset - 2];
            let trail = bytes[offset - 1];
            if (0xA1..=0xFE).contains(&lead) && (0xA1..=0xFE).contains(&trail) {
                // Check it's not part of a 3-byte sequence
                if offset >= 3 && bytes[offset - 3] == 0x8F {
                    // This is actually a 3-byte sequence
                } else {
                    let pointer = ((lead - 0xA1) as u16) * 94 + (trail - 0xA1) as u16;
                    if let Some(c) = jis0208_lookup(pointer) {
                        return Some((c, offset - 2));
                    }
                }
            }
        }

        // Try 3-byte JIS X 0212
        if offset >= 3 {
            let b1 = bytes[offset - 3];
            let b2 = bytes[offset - 2];
            let b3 = bytes[offset - 1];
            if b1 == 0x8F && (0xA1..=0xFE).contains(&b2) && (0xA1..=0xFE).contains(&b3) {
                let pointer = ((b2 - 0xA1) as u16) * 94 + (b3 - 0xA1) as u16;
                if let Some(c) = jis0212_lookup(pointer) {
                    return Some((c, offset - 3));
                }
            }
        }

        None
    }
}

/// Look up a character in the JIS X 0208 decode table.
fn jis0208_lookup(pointer: u16) -> Option<char> {
    JIS0208_DECODE
        .binary_search_by_key(&pointer, |&(p, _)| p)
        .ok()
        .map(|i| JIS0208_DECODE[i].1)
}

/// Look up the pointer for a character in JIS X 0208.
fn jis0208_encode_lookup(c: char) -> Option<u16> {
    JIS0208_ENCODE
        .binary_search_by_key(&c, |&(ch, _)| ch)
        .ok()
        .map(|i| JIS0208_ENCODE[i].1)
}

/// Look up a character in the JIS X 0212 decode table.
fn jis0212_lookup(pointer: u16) -> Option<char> {
    JIS0212_DECODE
        .binary_search_by_key(&pointer, |&(p, _)| p)
        .ok()
        .map(|i| JIS0212_DECODE[i].1)
}

impl crate::encoding::LimitedEncoding for EucJp {}

#[cfg(feature = "registry")]
inventory::submit! {
    crate::registry::EncodingEntry {
        name: "EUC-JP",
        aliases: &["euc-jp", "eucjp", "EUC_JP", "x-euc-jp"],
        is_unicode: false,
        decode: |bytes| {
            EucJp::validate(bytes)?;
            let mut chars = Vec::new();
            let mut offset = 0;
            while let Some((c, next)) = EucJp::decode_char_at(bytes, offset) {
                chars.push(c);
                offset = next;
            }
            Ok(chars)
        },
        try_encode_char: |c| {
            let mut buf = [0u8; 3];
            EucJp::try_encode_char(c, &mut buf).map(|len| buf[..len].to_vec())
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ascii() {
        let mut buf = [0u8; 3];
        assert_eq!(EucJp::encode_char('A', &mut buf), 1);
        assert_eq!(buf[0], b'A');

        let bytes = b"Hello";
        assert_eq!(EucJp::decode_char_at(bytes, 0), Some(('H', 1)));
    }

    #[test]
    fn test_hiragana() {
        // Test hiragana 'あ' (U+3042) - should be in JIS X 0208
        let mut buf = [0u8; 3];
        let len = EucJp::encode_char('あ', &mut buf);
        assert_eq!(len, 2);

        // Decode it back
        let decoded = EucJp::decode_char_at(&buf[..len], 0);
        assert_eq!(decoded, Some(('あ', 2)));
    }

    #[test]
    fn test_katakana() {
        // Test katakana 'ア' (U+30A2) - should be in JIS X 0208
        let mut buf = [0u8; 3];
        let len = EucJp::encode_char('ア', &mut buf);
        assert_eq!(len, 2);

        let decoded = EucJp::decode_char_at(&buf[..len], 0);
        assert_eq!(decoded, Some(('ア', 2)));
    }

    #[test]
    fn test_half_width_katakana() {
        // Test half-width katakana 'ア' (U+FF71)
        let mut buf = [0u8; 3];
        let len = EucJp::encode_char('\u{FF71}', &mut buf);
        assert_eq!(len, 2);
        assert_eq!(buf[0], 0x8E);

        let decoded = EucJp::decode_char_at(&buf[..len], 0);
        assert_eq!(decoded, Some(('\u{FF71}', 2)));
    }

    #[test]
    fn test_kanji() {
        // Test kanji '日' (U+65E5) - common kanji
        let mut buf = [0u8; 3];
        let len = EucJp::encode_char('日', &mut buf);
        assert_eq!(len, 2);

        let decoded = EucJp::decode_char_at(&buf[..len], 0);
        assert_eq!(decoded, Some(('日', 2)));
    }

    #[test]
    fn test_validate() {
        // Valid ASCII
        assert!(EucJp::validate(b"Hello").is_ok());

        // Valid JIS X 0208 (encoded 'あ')
        let mut buf = [0u8; 2];
        EucJp::encode_char('あ', &mut buf);
        assert!(EucJp::validate(&buf).is_ok());

        // Invalid: truncated sequence
        assert!(EucJp::validate(&[0xA4]).is_err());

        // Invalid: bad lead byte
        assert!(EucJp::validate(&[0x80]).is_err());
    }

    #[test]
    fn test_roundtrip() {
        let chars = ['A', 'あ', 'ア', '日', '本', '\u{FF71}'];
        for c in chars {
            let mut buf = [0u8; 3];
            let len = EucJp::encode_char(c, &mut buf);
            let decoded = EucJp::decode_char_at(&buf[..len], 0);
            assert_eq!(decoded, Some((c, len)), "Failed roundtrip for {:?}", c);
        }
    }
}
