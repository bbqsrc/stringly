use crate::encoding::Encoding;
use crate::error::EncodingError;

/// UTF-32 Little Endian encoding marker.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Utf32Le;

// Surrogate range constants (invalid in UTF-32)
const SURROGATE_START: u32 = 0xD800;
const SURROGATE_END: u32 = 0xDFFF;
const MAX_CODE_POINT: u32 = 0x10FFFF;

impl Encoding for Utf32Le {
    const NAME: &'static str = "UTF-32LE";
    const IS_FIXED_WIDTH: bool = true;
    const BYTES_PER_CHAR: Option<usize> = Some(4);
    const MAX_CHAR_LEN: usize = 4;

    fn validate(bytes: &[u8]) -> Result<(), EncodingError> {
        // Must have length divisible by 4
        if bytes.len() % 4 != 0 {
            return Err(EncodingError::new(
                bytes.len() - (bytes.len() % 4),
                Some(bytes.len() % 4),
            ));
        }

        let mut offset = 0;
        while offset < bytes.len() {
            let cp = u32::from_le_bytes([
                bytes[offset],
                bytes[offset + 1],
                bytes[offset + 2],
                bytes[offset + 3],
            ]);

            // Check for surrogate range (invalid in UTF-32)
            if (SURROGATE_START..=SURROGATE_END).contains(&cp) {
                return Err(EncodingError::new(offset, Some(4)));
            }

            // Check for out-of-range code point
            if cp > MAX_CODE_POINT {
                return Err(EncodingError::new(offset, Some(4)));
            }

            offset += 4;
        }

        Ok(())
    }

    fn decode_char_at(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        if offset + 4 > bytes.len() {
            return None;
        }

        let cp = u32::from_le_bytes([
            bytes[offset],
            bytes[offset + 1],
            bytes[offset + 2],
            bytes[offset + 3],
        ]);

        let c = char::from_u32(cp)?;
        Some((c, offset + 4))
    }

    fn encoded_len(_c: char) -> usize {
        4
    }

    fn encode_char(c: char, buf: &mut [u8]) -> usize {
        let bytes = (c as u32).to_le_bytes();
        buf[0] = bytes[0];
        buf[1] = bytes[1];
        buf[2] = bytes[2];
        buf[3] = bytes[3];
        4
    }

    fn is_char_boundary(bytes: &[u8], index: usize) -> bool {
        index % 4 == 0 && index <= bytes.len()
    }

    fn decode_char_before(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        if offset < 4 || offset > bytes.len() {
            return None;
        }

        // Must be on 4-byte boundary
        if offset % 4 != 0 {
            return None;
        }

        let cp = u32::from_le_bytes([
            bytes[offset - 4],
            bytes[offset - 3],
            bytes[offset - 2],
            bytes[offset - 1],
        ]);

        let c = char::from_u32(cp)?;
        Some((c, offset - 4))
    }
}

impl crate::encoding::UniversalEncoding for Utf32Le {}

// === Registry registration ===

#[cfg(feature = "registry")]
inventory::submit! {
    crate::registry::EncodingEntry {
        name: "UTF-32LE",
        aliases: &["UTF32LE", "utf-32le", "utf32le", "UCS-4LE", "ucs-4le"],
        is_unicode: true,
        decode: |bytes| {
            Utf32Le::validate(bytes)?;
            let mut chars = Vec::new();
            let mut offset = 0;
            while let Some((c, next)) = Utf32Le::decode_char_at(bytes, offset) {
                chars.push(c);
                offset = next;
            }
            Ok(chars)
        },
        try_encode_char: |c| {
            let mut buf = [0u8; 4];
            let len = Utf32Le::encode_char(c, &mut buf);
            Some(buf[..len].to_vec())
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validate_ascii() {
        // "hello" in UTF-32LE
        let bytes = [
            0x68, 0x00, 0x00, 0x00, // 'h'
            0x65, 0x00, 0x00, 0x00, // 'e'
            0x6C, 0x00, 0x00, 0x00, // 'l'
            0x6C, 0x00, 0x00, 0x00, // 'l'
            0x6F, 0x00, 0x00, 0x00, // 'o'
        ];
        assert!(Utf32Le::validate(&bytes).is_ok());
    }

    #[test]
    fn test_validate_wrong_length() {
        let bytes = [0x68, 0x00, 0x00]; // Only 3 bytes
        assert!(Utf32Le::validate(&bytes).is_err());

        let bytes = [0x68, 0x00, 0x00, 0x00, 0x65]; // 5 bytes
        assert!(Utf32Le::validate(&bytes).is_err());
    }

    #[test]
    fn test_validate_emoji() {
        // U+1F600 (😀)
        let bytes = [0x00, 0xF6, 0x01, 0x00];
        assert!(Utf32Le::validate(&bytes).is_ok());
    }

    #[test]
    fn test_validate_surrogate() {
        // Surrogate code points are invalid in UTF-32
        // U+D800 (high surrogate start)
        let bytes = [0x00, 0xD8, 0x00, 0x00];
        assert!(Utf32Le::validate(&bytes).is_err());

        // U+DFFF (low surrogate end)
        let bytes = [0xFF, 0xDF, 0x00, 0x00];
        assert!(Utf32Le::validate(&bytes).is_err());
    }

    #[test]
    fn test_validate_out_of_range() {
        // Code points above U+10FFFF are invalid
        let bytes = [0x00, 0x00, 0x11, 0x00]; // U+110000
        assert!(Utf32Le::validate(&bytes).is_err());
    }

    #[test]
    fn test_decode_ascii() {
        let bytes = [0x68, 0x00, 0x00, 0x00]; // 'h'
        let (c, next) = Utf32Le::decode_char_at(&bytes, 0).unwrap();
        assert_eq!(c, 'h');
        assert_eq!(next, 4);
    }

    #[test]
    fn test_decode_emoji() {
        // U+1F600 (😀)
        let bytes = [0x00, 0xF6, 0x01, 0x00];
        let (c, next) = Utf32Le::decode_char_at(&bytes, 0).unwrap();
        assert_eq!(c, '😀');
        assert_eq!(next, 4);
    }

    #[test]
    fn test_encode_ascii() {
        let mut buf = [0u8; 4];
        let len = Utf32Le::encode_char('h', &mut buf);
        assert_eq!(len, 4);
        assert_eq!(&buf, &[0x68, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_encode_emoji() {
        let mut buf = [0u8; 4];
        let len = Utf32Le::encode_char('😀', &mut buf);
        assert_eq!(len, 4);
        assert_eq!(&buf, &[0x00, 0xF6, 0x01, 0x00]);
    }

    #[test]
    fn test_is_char_boundary() {
        // "hi" in UTF-32LE
        let bytes = [
            0x68, 0x00, 0x00, 0x00, // 'h'
            0x69, 0x00, 0x00, 0x00, // 'i'
        ];

        assert!(Utf32Le::is_char_boundary(&bytes, 0));
        assert!(!Utf32Le::is_char_boundary(&bytes, 1));
        assert!(!Utf32Le::is_char_boundary(&bytes, 2));
        assert!(!Utf32Le::is_char_boundary(&bytes, 3));
        assert!(Utf32Le::is_char_boundary(&bytes, 4));
        assert!(!Utf32Le::is_char_boundary(&bytes, 5));
        assert!(!Utf32Le::is_char_boundary(&bytes, 6));
        assert!(!Utf32Le::is_char_boundary(&bytes, 7));
        assert!(Utf32Le::is_char_boundary(&bytes, 8));
    }

    #[test]
    fn test_decode_char_before() {
        // "hi" in UTF-32LE
        let bytes = [
            0x68, 0x00, 0x00, 0x00, // 'h'
            0x69, 0x00, 0x00, 0x00, // 'i'
        ];

        let (c, start) = Utf32Le::decode_char_before(&bytes, 8).unwrap();
        assert_eq!(c, 'i');
        assert_eq!(start, 4);

        let (c, start) = Utf32Le::decode_char_before(&bytes, 4).unwrap();
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
            let len = Utf32Le::encode_char(c, &mut buf);
            let (decoded, _) = Utf32Le::decode_char_at(&buf[..len], 0).unwrap();
            assert_eq!(decoded, c, "roundtrip failed for U+{:04X}", cp);
        }
    }

    #[test]
    fn test_roundtrip_supplementary() {
        let mut buf = [0u8; 4];
        for cp in 0x10000u32..=0x10FFFF {
            let c = char::from_u32(cp).unwrap();
            let len = Utf32Le::encode_char(c, &mut buf);
            let (decoded, _) = Utf32Le::decode_char_at(&buf[..len], 0).unwrap();
            assert_eq!(decoded, c, "roundtrip failed for U+{:04X}", cp);
        }
    }
}
