use crate::encoding::Encoding;
use crate::error::EncodingError;

/// UTF-16 Big Endian encoding marker.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Utf16Be;

// Surrogate range constants
const SURROGATE_HIGH_START: u16 = 0xD800;
const SURROGATE_HIGH_END: u16 = 0xDBFF;
const SURROGATE_LOW_START: u16 = 0xDC00;
const SURROGATE_LOW_END: u16 = 0xDFFF;

impl Encoding for Utf16Be {
    const NAME: &'static str = "UTF-16BE";
    const IS_FIXED_WIDTH: bool = false;
    const BYTES_PER_CHAR: Option<usize> = None;
    const MAX_CHAR_LEN: usize = 4;
    const NULL_LEN: usize = 2;

    fn validate(bytes: &[u8]) -> Result<(), EncodingError> {
        // Must have even number of bytes
        if bytes.len() % 2 != 0 {
            return Err(EncodingError::new(bytes.len() - 1, Some(1)));
        }

        let mut offset = 0;
        while offset < bytes.len() {
            let unit = u16::from_be_bytes([bytes[offset], bytes[offset + 1]]);

            if (SURROGATE_HIGH_START..=SURROGATE_HIGH_END).contains(&unit) {
                // High surrogate - must be followed by low surrogate
                if offset + 4 > bytes.len() {
                    return Err(EncodingError::new(offset, Some(2)));
                }
                let low = u16::from_be_bytes([bytes[offset + 2], bytes[offset + 3]]);
                if !(SURROGATE_LOW_START..=SURROGATE_LOW_END).contains(&low) {
                    return Err(EncodingError::new(offset, Some(2)));
                }
                offset += 4;
            } else if (SURROGATE_LOW_START..=SURROGATE_LOW_END).contains(&unit) {
                // Lone low surrogate is invalid
                return Err(EncodingError::new(offset, Some(2)));
            } else {
                // BMP character
                offset += 2;
            }
        }

        Ok(())
    }

    fn decode_char_at(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        if offset + 2 > bytes.len() {
            return None;
        }

        let unit = u16::from_be_bytes([bytes[offset], bytes[offset + 1]]);

        if (SURROGATE_HIGH_START..=SURROGATE_HIGH_END).contains(&unit) {
            // Surrogate pair
            if offset + 4 > bytes.len() {
                return None;
            }
            let low = u16::from_be_bytes([bytes[offset + 2], bytes[offset + 3]]);
            if !(SURROGATE_LOW_START..=SURROGATE_LOW_END).contains(&low) {
                return None;
            }

            let high = unit - SURROGATE_HIGH_START;
            let low = low - SURROGATE_LOW_START;
            let cp = 0x10000 + ((high as u32) << 10) + (low as u32);
            let c = char::from_u32(cp)?;
            Some((c, offset + 4))
        } else if (SURROGATE_LOW_START..=SURROGATE_LOW_END).contains(&unit) {
            // Lone low surrogate
            None
        } else {
            // BMP character
            let c = char::from_u32(unit as u32)?;
            Some((c, offset + 2))
        }
    }

    fn encoded_len(c: char) -> usize {
        let cp = c as u32;
        if cp < 0x10000 { 2 } else { 4 }
    }

    fn encode_char(c: char, buf: &mut [u8]) -> usize {
        let cp = c as u32;

        if cp < 0x10000 {
            let bytes = (cp as u16).to_be_bytes();
            buf[0] = bytes[0];
            buf[1] = bytes[1];
            2
        } else {
            // Surrogate pair
            let cp = cp - 0x10000;
            let high = SURROGATE_HIGH_START + ((cp >> 10) as u16);
            let low = SURROGATE_LOW_START + ((cp & 0x3FF) as u16);

            let high_bytes = high.to_be_bytes();
            let low_bytes = low.to_be_bytes();

            buf[0] = high_bytes[0];
            buf[1] = high_bytes[1];
            buf[2] = low_bytes[0];
            buf[3] = low_bytes[1];
            4
        }
    }

    fn is_char_boundary(bytes: &[u8], index: usize) -> bool {
        if index == 0 || index == bytes.len() {
            return true;
        }

        // Must be on a 2-byte boundary
        if index % 2 != 0 {
            return false;
        }

        if index + 2 > bytes.len() {
            return false;
        }

        // Check if this is a low surrogate (would mean we're in the middle of a char)
        let unit = u16::from_be_bytes([bytes[index], bytes[index + 1]]);
        !(SURROGATE_LOW_START..=SURROGATE_LOW_END).contains(&unit)
    }

    fn decode_char_before(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        if offset < 2 || offset > bytes.len() {
            return None;
        }

        // Must be on 2-byte boundary
        if offset % 2 != 0 {
            return None;
        }

        let prev_unit = u16::from_be_bytes([bytes[offset - 2], bytes[offset - 1]]);

        if (SURROGATE_LOW_START..=SURROGATE_LOW_END).contains(&prev_unit) {
            // This is a low surrogate, look for high surrogate before it
            if offset < 4 {
                return None;
            }
            let high_unit = u16::from_be_bytes([bytes[offset - 4], bytes[offset - 3]]);
            if !(SURROGATE_HIGH_START..=SURROGATE_HIGH_END).contains(&high_unit) {
                return None;
            }

            let high = high_unit - SURROGATE_HIGH_START;
            let low = prev_unit - SURROGATE_LOW_START;
            let cp = 0x10000 + ((high as u32) << 10) + (low as u32);
            let c = char::from_u32(cp)?;
            Some((c, offset - 4))
        } else if (SURROGATE_HIGH_START..=SURROGATE_HIGH_END).contains(&prev_unit) {
            // Lone high surrogate
            None
        } else {
            // BMP character
            let c = char::from_u32(prev_unit as u32)?;
            Some((c, offset - 2))
        }
    }
}

impl crate::encoding::UniversalEncoding for Utf16Be {}

// === Registry registration ===

#[cfg(feature = "registry")]
inventory::submit! {
    crate::registry::EncodingEntry {
        name: "UTF-16BE",
        aliases: &["UTF16BE", "utf-16be", "utf16be", "UCS-2BE", "ucs-2be"],
        is_unicode: true,
        decode: |bytes| {
            Utf16Be::validate(bytes)?;
            let mut chars = Vec::new();
            let mut offset = 0;
            while let Some((c, next)) = Utf16Be::decode_char_at(bytes, offset) {
                chars.push(c);
                offset = next;
            }
            Ok(chars)
        },
        try_encode_char: |c| {
            let mut buf = [0u8; 4];
            let len = Utf16Be::encode_char(c, &mut buf);
            Some(buf[..len].to_vec())
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validate_bmp() {
        // "hello" in UTF-16BE
        let bytes = [0x00, 0x68, 0x00, 0x65, 0x00, 0x6C, 0x00, 0x6C, 0x00, 0x6F];
        assert!(Utf16Be::validate(&bytes).is_ok());
    }

    #[test]
    fn test_validate_odd_length() {
        let bytes = [0x00, 0x68, 0x00];
        assert!(Utf16Be::validate(&bytes).is_err());
    }

    #[test]
    fn test_validate_surrogate_pair() {
        // U+1F600 (😀) = D83D DE00 in UTF-16BE
        let bytes = [0xD8, 0x3D, 0xDE, 0x00];
        assert!(Utf16Be::validate(&bytes).is_ok());
    }

    #[test]
    fn test_validate_lone_surrogate() {
        // Lone high surrogate
        let bytes = [0xD8, 0x3D, 0x00, 0x68];
        assert!(Utf16Be::validate(&bytes).is_err());

        // Lone low surrogate
        let bytes = [0xDE, 0x00, 0x00, 0x68];
        assert!(Utf16Be::validate(&bytes).is_err());
    }

    #[test]
    fn test_decode_bmp() {
        let bytes = [0x00, 0x68]; // 'h'
        let (c, next) = Utf16Be::decode_char_at(&bytes, 0).unwrap();
        assert_eq!(c, 'h');
        assert_eq!(next, 2);
    }

    #[test]
    fn test_decode_surrogate_pair() {
        // U+1F600 (😀)
        let bytes = [0xD8, 0x3D, 0xDE, 0x00];
        let (c, next) = Utf16Be::decode_char_at(&bytes, 0).unwrap();
        assert_eq!(c, '😀');
        assert_eq!(next, 4);
    }

    #[test]
    fn test_encode_bmp() {
        let mut buf = [0u8; 4];
        let len = Utf16Be::encode_char('h', &mut buf);
        assert_eq!(len, 2);
        assert_eq!(&buf[..2], &[0x00, 0x68]);
    }

    #[test]
    fn test_encode_surrogate_pair() {
        let mut buf = [0u8; 4];
        let len = Utf16Be::encode_char('😀', &mut buf);
        assert_eq!(len, 4);
        assert_eq!(&buf[..4], &[0xD8, 0x3D, 0xDE, 0x00]);
    }

    #[test]
    fn test_is_char_boundary() {
        // "h😀" in UTF-16BE
        let bytes = [0x00, 0x68, 0xD8, 0x3D, 0xDE, 0x00];

        assert!(Utf16Be::is_char_boundary(&bytes, 0));
        assert!(!Utf16Be::is_char_boundary(&bytes, 1)); // Middle of 'h'
        assert!(Utf16Be::is_char_boundary(&bytes, 2)); // Start of emoji
        assert!(!Utf16Be::is_char_boundary(&bytes, 3)); // Middle of high surrogate
        assert!(!Utf16Be::is_char_boundary(&bytes, 4)); // Low surrogate (middle of emoji)
        assert!(!Utf16Be::is_char_boundary(&bytes, 5)); // Middle of low surrogate
        assert!(Utf16Be::is_char_boundary(&bytes, 6)); // End
    }

    #[test]
    fn test_decode_char_before() {
        // "h😀" in UTF-16BE
        let bytes = [0x00, 0x68, 0xD8, 0x3D, 0xDE, 0x00];

        let (c, start) = Utf16Be::decode_char_before(&bytes, 6).unwrap();
        assert_eq!(c, '😀');
        assert_eq!(start, 2);

        let (c, start) = Utf16Be::decode_char_before(&bytes, 2).unwrap();
        assert_eq!(c, 'h');
        assert_eq!(start, 0);
    }

    #[test]
    fn test_roundtrip_all_bmp() {
        let mut buf = [0u8; 4];
        for cp in 0u32..0x10000 {
            // Skip surrogates
            if (0xD800..=0xDFFF).contains(&cp) {
                continue;
            }
            let c = char::from_u32(cp).unwrap();
            let len = Utf16Be::encode_char(c, &mut buf);
            let (decoded, _) = Utf16Be::decode_char_at(&buf[..len], 0).unwrap();
            assert_eq!(decoded, c, "roundtrip failed for U+{:04X}", cp);
        }
    }

    #[test]
    fn test_roundtrip_supplementary() {
        let mut buf = [0u8; 4];
        for cp in 0x10000u32..=0x10FFFF {
            let c = char::from_u32(cp).unwrap();
            let len = Utf16Be::encode_char(c, &mut buf);
            let (decoded, _) = Utf16Be::decode_char_at(&buf[..len], 0).unwrap();
            assert_eq!(decoded, c, "roundtrip failed for U+{:04X}", cp);
        }
    }
}
