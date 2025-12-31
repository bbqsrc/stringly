//! CESU-8 encoding implementation.
//!
//! CESU-8 (Compatibility Encoding Scheme for UTF-16) is a variant of UTF-8 that encodes
//! supplementary characters (U+10000 and above) as two separate 3-byte sequences representing
//! the UTF-16 surrogate pair, rather than as a single 4-byte UTF-8 sequence.
//!
//! # Comparison with UTF-8
//!
//! | Character Range | UTF-8 | CESU-8 |
//! |-----------------|-------|--------|
//! | U+0000-U+007F | 1 byte | 1 byte |
//! | U+0080-U+07FF | 2 bytes | 2 bytes |
//! | U+0800-U+FFFF | 3 bytes | 3 bytes |
//! | U+10000-U+10FFFF | 4 bytes | 6 bytes (surrogate pair) |
//!
//! # Usage
//!
//! CESU-8 is found in Oracle databases and some Java serialization contexts where
//! the "Modified UTF-8" format is used.

use alloc::vec::Vec;

use crate::encoding::{Encoding, UniversalEncoding};
use crate::error::EncodingError;

/// CESU-8 encoding marker.
///
/// CESU-8 encodes supplementary Unicode characters (U+10000 and above) as two
/// 3-byte sequences representing UTF-16 surrogate pairs, resulting in 6 bytes
/// instead of UTF-8's 4 bytes for these characters.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Cesu8;

/// High surrogate range: U+D800 to U+DBFF
const SURROGATE_HIGH_START: u32 = 0xD800;
const SURROGATE_HIGH_END: u32 = 0xDBFF;

/// Low surrogate range: U+DC00 to U+DFFF
const SURROGATE_LOW_START: u32 = 0xDC00;
const SURROGATE_LOW_END: u32 = 0xDFFF;

impl Encoding for Cesu8 {
    const NAME: &'static str = "CESU-8";
    const IS_FIXED_WIDTH: bool = false;
    const BYTES_PER_CHAR: Option<usize> = None;
    const MAX_CHAR_LEN: usize = 6; // Surrogate pairs take 6 bytes

    fn validate(bytes: &[u8]) -> Result<(), EncodingError> {
        let mut i = 0;
        while i < bytes.len() {
            let b = bytes[i];
            let (len, codepoint) = if b < 0x80 {
                // ASCII
                (1, b as u32)
            } else if b & 0xE0 == 0xC0 {
                // 2-byte sequence
                if i + 1 >= bytes.len() {
                    return Err(EncodingError::new(i, Some(bytes.len() - i)));
                }
                if !is_continuation(bytes[i + 1]) {
                    return Err(EncodingError::new(i, Some(2)));
                }
                let cp = ((b as u32 & 0x1F) << 6) | (bytes[i + 1] as u32 & 0x3F);
                // Check for overlong encoding
                if cp < 0x80 {
                    return Err(EncodingError::new(i, Some(2)));
                }
                (2, cp)
            } else if b & 0xF0 == 0xE0 {
                // 3-byte sequence
                if i + 2 >= bytes.len() {
                    return Err(EncodingError::new(i, Some(bytes.len() - i)));
                }
                if !is_continuation(bytes[i + 1]) || !is_continuation(bytes[i + 2]) {
                    return Err(EncodingError::new(i, Some(3)));
                }
                let cp = ((b as u32 & 0x0F) << 12)
                    | ((bytes[i + 1] as u32 & 0x3F) << 6)
                    | (bytes[i + 2] as u32 & 0x3F);
                // Check for overlong encoding
                if cp < 0x800 {
                    return Err(EncodingError::new(i, Some(3)));
                }
                // If this is a high surrogate, we need a low surrogate to follow
                if is_high_surrogate(cp) {
                    if i + 5 >= bytes.len() {
                        return Err(EncodingError::new(i, Some(bytes.len() - i)));
                    }
                    // Check the next 3 bytes form a low surrogate
                    let b2 = bytes[i + 3];
                    if b2 & 0xF0 != 0xE0 {
                        return Err(EncodingError::new(i + 3, Some(1)));
                    }
                    if !is_continuation(bytes[i + 4]) || !is_continuation(bytes[i + 5]) {
                        return Err(EncodingError::new(i + 3, Some(3)));
                    }
                    let low_cp = ((b2 as u32 & 0x0F) << 12)
                        | ((bytes[i + 4] as u32 & 0x3F) << 6)
                        | (bytes[i + 5] as u32 & 0x3F);
                    if !is_low_surrogate(low_cp) {
                        return Err(EncodingError::new(i + 3, Some(3)));
                    }
                    // Valid surrogate pair, skip the full 6 bytes
                    i += 6;
                    continue;
                }
                // Lone low surrogate is invalid
                if is_low_surrogate(cp) {
                    return Err(EncodingError::new(i, Some(3)));
                }
                (3, cp)
            } else if b & 0xF8 == 0xF0 {
                // 4-byte sequence - NOT valid in CESU-8
                // CESU-8 uses surrogate pairs instead
                return Err(EncodingError::new(i, Some(1)));
            } else {
                // Invalid start byte
                return Err(EncodingError::new(i, Some(1)));
            };

            // Check the codepoint is valid
            if codepoint > 0x10FFFF {
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

        let b = bytes[offset];

        if b < 0x80 {
            // ASCII
            return Some((b as char, offset + 1));
        }

        if b & 0xE0 == 0xC0 {
            // 2-byte sequence
            if offset + 1 >= bytes.len() {
                return None;
            }
            let cp = ((b as u32 & 0x1F) << 6) | (bytes[offset + 1] as u32 & 0x3F);
            return char::from_u32(cp).map(|c| (c, offset + 2));
        }

        if b & 0xF0 == 0xE0 {
            // 3-byte sequence
            if offset + 2 >= bytes.len() {
                return None;
            }
            let cp = ((b as u32 & 0x0F) << 12)
                | ((bytes[offset + 1] as u32 & 0x3F) << 6)
                | (bytes[offset + 2] as u32 & 0x3F);

            // Check if this is a high surrogate (start of surrogate pair)
            if is_high_surrogate(cp) {
                // Need to decode the following low surrogate
                if offset + 5 >= bytes.len() {
                    return None;
                }
                let b2 = bytes[offset + 3];
                if b2 & 0xF0 != 0xE0 {
                    return None;
                }
                let low_cp = ((b2 as u32 & 0x0F) << 12)
                    | ((bytes[offset + 4] as u32 & 0x3F) << 6)
                    | (bytes[offset + 5] as u32 & 0x3F);

                if !is_low_surrogate(low_cp) {
                    return None;
                }

                // Combine surrogate pair into supplementary codepoint
                let high = cp - SURROGATE_HIGH_START;
                let low = low_cp - SURROGATE_LOW_START;
                let codepoint = 0x10000 + ((high << 10) | low);
                return char::from_u32(codepoint).map(|c| (c, offset + 6));
            }

            // Regular BMP character (but not a lone low surrogate)
            if is_low_surrogate(cp) {
                return None;
            }

            return char::from_u32(cp).map(|c| (c, offset + 3));
        }

        // 4-byte sequences are not valid in CESU-8
        None
    }

    fn encoded_len(c: char) -> usize {
        let cp = c as u32;
        if cp < 0x80 {
            1
        } else if cp < 0x800 {
            2
        } else if cp < 0x10000 {
            3
        } else {
            // Supplementary characters use surrogate pairs (6 bytes)
            6
        }
    }

    fn encode_char(c: char, buf: &mut [u8]) -> usize {
        let cp = c as u32;

        if cp < 0x80 {
            buf[0] = cp as u8;
            1
        } else if cp < 0x800 {
            buf[0] = 0xC0 | ((cp >> 6) as u8);
            buf[1] = 0x80 | ((cp & 0x3F) as u8);
            2
        } else if cp < 0x10000 {
            buf[0] = 0xE0 | ((cp >> 12) as u8);
            buf[1] = 0x80 | (((cp >> 6) & 0x3F) as u8);
            buf[2] = 0x80 | ((cp & 0x3F) as u8);
            3
        } else {
            // Supplementary character: encode as surrogate pair
            let adjusted = cp - 0x10000;
            let high = SURROGATE_HIGH_START + (adjusted >> 10);
            let low = SURROGATE_LOW_START + (adjusted & 0x3FF);

            // Encode high surrogate
            buf[0] = 0xE0 | ((high >> 12) as u8);
            buf[1] = 0x80 | (((high >> 6) & 0x3F) as u8);
            buf[2] = 0x80 | ((high & 0x3F) as u8);

            // Encode low surrogate
            buf[3] = 0xE0 | ((low >> 12) as u8);
            buf[4] = 0x80 | (((low >> 6) & 0x3F) as u8);
            buf[5] = 0x80 | ((low & 0x3F) as u8);

            6
        }
    }

    fn is_char_boundary(bytes: &[u8], index: usize) -> bool {
        if index == 0 || index >= bytes.len() {
            return true;
        }
        // Same as UTF-8: continuation bytes have pattern 10xxxxxx
        !is_continuation(bytes[index])
    }

    fn decode_char_before(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        if offset == 0 || offset > bytes.len() {
            return None;
        }

        // Scan backwards to find the start of a 3-byte sequence
        let mut start = offset - 1;
        while start > 0 && is_continuation(bytes[start]) {
            start -= 1;
        }

        // Try to decode at start
        if let Some((c, end)) = Self::decode_char_at(bytes, start) {
            if end == offset {
                return Some((c, start));
            }
        }

        // If that failed or didn't end at offset, this might be the low surrogate
        // of a surrogate pair. Try 3 bytes earlier for the high surrogate.
        if start >= 3 {
            if let Some((c, end)) = Self::decode_char_at(bytes, start - 3) {
                if end == offset {
                    return Some((c, start - 3));
                }
            }
        }

        None
    }
}

impl UniversalEncoding for Cesu8 {}

/// Returns true if the byte is a continuation byte (10xxxxxx).
#[inline]
fn is_continuation(b: u8) -> bool {
    (b & 0xC0) == 0x80
}

/// Returns true if the codepoint is a high surrogate (U+D800-U+DBFF).
#[inline]
fn is_high_surrogate(cp: u32) -> bool {
    cp >= SURROGATE_HIGH_START && cp <= SURROGATE_HIGH_END
}

/// Returns true if the codepoint is a low surrogate (U+DC00-U+DFFF).
#[inline]
fn is_low_surrogate(cp: u32) -> bool {
    cp >= SURROGATE_LOW_START && cp <= SURROGATE_LOW_END
}

#[cfg(feature = "registry")]
inventory::submit! {
    crate::registry::EncodingEntry {
        name: "CESU-8",
        aliases: &["CESU8", "cesu-8", "cesu8"],
        is_unicode: true,
        decode: |bytes| {
            Cesu8::validate(bytes)?;
            let mut result = Vec::new();
            let mut offset = 0;
            while let Some((c, next)) = Cesu8::decode_char_at(bytes, offset) {
                result.push(c);
                offset = next;
            }
            Ok(result)
        },
        try_encode_char: |c| {
            let mut buf = [0u8; 6];
            let len = Cesu8::encode_char(c, &mut buf);
            Some(buf[..len].to_vec())
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ascii() {
        assert!(Cesu8::validate(b"hello").is_ok());
        let (c, next) = Cesu8::decode_char_at(b"hello", 0).unwrap();
        assert_eq!(c, 'h');
        assert_eq!(next, 1);
    }

    #[test]
    fn test_bmp() {
        // é is U+00E9, same encoding as UTF-8
        let bytes = "héllo".as_bytes();
        assert!(Cesu8::validate(bytes).is_ok());

        // 日 is U+65E5
        let bytes = "日本語".as_bytes();
        assert!(Cesu8::validate(bytes).is_ok());
    }

    #[test]
    fn test_supplementary_encode() {
        // U+10000 should be encoded as surrogate pair
        let mut buf = [0u8; 6];
        let len = Cesu8::encode_char('\u{10000}', &mut buf);
        assert_eq!(len, 6);

        // D800 DC00 in "UTF-8 like" encoding:
        // D800 = 1101 1000 0000 0000 -> E0 DA 80 -> ED A0 80
        // DC00 = 1101 1100 0000 0000 -> E0 DB 00 -> ED B0 80
        assert_eq!(&buf[..6], &[0xED, 0xA0, 0x80, 0xED, 0xB0, 0x80]);
    }

    #[test]
    fn test_supplementary_decode() {
        // U+10000 encoded as surrogate pair
        let bytes = [0xED, 0xA0, 0x80, 0xED, 0xB0, 0x80];
        assert!(Cesu8::validate(&bytes).is_ok());

        let (c, next) = Cesu8::decode_char_at(&bytes, 0).unwrap();
        assert_eq!(c, '\u{10000}');
        assert_eq!(next, 6);
    }

    #[test]
    fn test_emoji() {
        // 😀 is U+1F600
        let mut buf = [0u8; 6];
        let len = Cesu8::encode_char('😀', &mut buf);
        assert_eq!(len, 6);

        // Validate and decode
        assert!(Cesu8::validate(&buf).is_ok());
        let (c, _) = Cesu8::decode_char_at(&buf, 0).unwrap();
        assert_eq!(c, '😀');
    }

    #[test]
    fn test_invalid_utf8_4byte() {
        // UTF-8 4-byte sequence for U+10000 is F0 90 80 80
        // This should be INVALID in CESU-8
        let utf8_4byte = [0xF0, 0x90, 0x80, 0x80];
        assert!(Cesu8::validate(&utf8_4byte).is_err());
    }

    #[test]
    fn test_lone_surrogate() {
        // A lone high surrogate (D800) encoded as 3 bytes
        let lone_high = [0xED, 0xA0, 0x80];
        assert!(Cesu8::validate(&lone_high).is_err());

        // A lone low surrogate (DC00) encoded as 3 bytes
        let lone_low = [0xED, 0xB0, 0x80];
        assert!(Cesu8::validate(&lone_low).is_err());
    }

    #[test]
    fn test_encoded_len() {
        assert_eq!(Cesu8::encoded_len('a'), 1);
        assert_eq!(Cesu8::encoded_len('é'), 2);
        assert_eq!(Cesu8::encoded_len('日'), 3);
        assert_eq!(Cesu8::encoded_len('😀'), 6);
    }

    #[test]
    fn test_is_char_boundary() {
        let bytes = [0xED, 0xA0, 0x80, 0xED, 0xB0, 0x80]; // U+10000
        assert!(Cesu8::is_char_boundary(&bytes, 0));
        assert!(!Cesu8::is_char_boundary(&bytes, 1));
        assert!(!Cesu8::is_char_boundary(&bytes, 2));
        assert!(Cesu8::is_char_boundary(&bytes, 3)); // Start of low surrogate
        assert!(!Cesu8::is_char_boundary(&bytes, 4));
        assert!(!Cesu8::is_char_boundary(&bytes, 5));
    }

    #[test]
    fn test_decode_char_before() {
        let bytes = [0xED, 0xA0, 0x80, 0xED, 0xB0, 0x80]; // U+10000
        let (c, start) = Cesu8::decode_char_before(&bytes, 6).unwrap();
        assert_eq!(c, '\u{10000}');
        assert_eq!(start, 0);
    }
}
