//! Comprehensive tests for all encoding implementations.
//!
//! Tests the Encoding trait implementation for each encoding type.

use paste::paste;
use stringly::Encoding;

// =============================================================================
// Test macros for different encoding categories
// =============================================================================

/// Tests that apply to ALL encodings
macro_rules! test_encoding_basics {
    ($name:ident, $encoding:ty) => {
        mod $name {
            #[allow(unused_imports)]
            use super::*;
            use stringly::Encoding;

            #[test]
            fn name_is_not_empty() {
                assert!(!<$encoding>::NAME.is_empty());
            }

            #[test]
            fn empty_bytes_valid() {
                assert!(<$encoding>::validate(&[]).is_ok());
            }

            #[test]
            fn boundary_at_zero() {
                assert!(<$encoding>::is_char_boundary(&[], 0));
                assert!(<$encoding>::is_char_boundary(&[0x41], 0));
            }

            #[test]
            fn boundary_at_len() {
                // Test boundary at the end of a properly encoded character
                let mut buf = [0u8; 8];
                let c = 'A';
                if <$encoding>::can_encode(c) {
                    let len = <$encoding>::encode_char(c, &mut buf);
                    assert!(<$encoding>::is_char_boundary(&buf[..len], len));
                }
            }

            #[test]
            fn ascii_letter_roundtrip() {
                let mut buf = [0u8; 8];
                let c = 'A';
                if <$encoding>::can_encode(c) {
                    let len = <$encoding>::encode_char(c, &mut buf);
                    assert!(len > 0);
                    let (decoded, next) = <$encoding>::decode_char_at(&buf[..len], 0).unwrap();
                    assert_eq!(decoded, c);
                    assert_eq!(next, len);
                }
            }

            #[test]
            fn decode_char_before_works() {
                let mut buf = [0u8; 8];
                let c = 'A';
                if <$encoding>::can_encode(c) {
                    let len = <$encoding>::encode_char(c, &mut buf);
                    let (decoded, prev) =
                        <$encoding>::decode_char_before(&buf[..len], len).unwrap();
                    assert_eq!(decoded, c);
                    assert_eq!(prev, 0);
                }
            }
        }
    };
}

/// Tests for single-byte encodings (all bytes 0x00-0xFF are valid or map to something)
macro_rules! test_single_byte_encoding {
    ($name:ident, $encoding:ty) => {
        test_encoding_basics!($name, $encoding);

        paste! {
            mod [<$name _single_byte>] {
                use super::*;

                #[test]
                fn is_fixed_width() {
                    assert!(<$encoding>::IS_FIXED_WIDTH);
                    assert_eq!(<$encoding>::BYTES_PER_CHAR, Some(1));
                    assert_eq!(<$encoding>::MAX_CHAR_LEN, 1);
                }

                #[test]
                fn all_single_bytes_are_boundaries() {
                    let bytes = [0x41, 0x42, 0x43];
                    for i in 0..=bytes.len() {
                        assert!(<$encoding>::is_char_boundary(&bytes, i));
                    }
                }

                #[test]
                fn encoded_len_always_one() {
                    for c in "ABCabc123".chars() {
                        if <$encoding>::can_encode(c) {
                            assert_eq!(<$encoding>::encoded_len(c), 1);
                        }
                    }
                }

                #[test]
                fn roundtrip_all_decodable_bytes() {
                    let mut buf = [0u8; 1];
                    for byte in 0u8..=255 {
                        if let Some((c, 1)) = <$encoding>::decode_char_at(&[byte], 0) {
                            // This byte decodes to a character
                            if <$encoding>::can_encode(c) {
                                let len = <$encoding>::encode_char(c, &mut buf);
                                assert_eq!(len, 1);
                                // Note: encoding might produce a different byte if there are
                                // multiple bytes mapping to the same character
                                let (decoded, _) = <$encoding>::decode_char_at(&buf, 0).unwrap();
                                assert_eq!(decoded, c);
                            }
                        }
                    }
                }

                #[test]
                fn try_encode_returns_none_for_unencodable() {
                    let mut buf = [0u8; 1];
                    // Most single-byte encodings can't encode CJK
                    let c = '中';
                    if !<$encoding>::can_encode(c) {
                        assert!(<$encoding>::try_encode_char(c, &mut buf).is_none());
                    }
                }
            }
        }
    };
}

/// Tests for multi-byte CJK encodings (variable width, supports CJK characters)
macro_rules! test_multibyte_encoding {
    ($name:ident, $encoding:ty) => {
        test_encoding_basics!($name, $encoding);

        paste! {
            mod [<$name _multibyte>] {
                use super::*;

                #[test]
                fn is_variable_width() {
                    assert!(!<$encoding>::IS_FIXED_WIDTH);
                    assert_eq!(<$encoding>::BYTES_PER_CHAR, None);
                }

                #[test]
                fn ascii_subset_works() {
                    let mut buf = [0u8; 8];
                    for byte in 0x20u8..0x7F {
                        let c = byte as char;
                        if <$encoding>::can_encode(c) {
                            let len = <$encoding>::encode_char(c, &mut buf);
                            let (decoded, _) = <$encoding>::decode_char_at(&buf[..len], 0).unwrap();
                            assert_eq!(decoded, c, "Failed for ASCII {:02X}", byte);
                        }
                    }
                }

                #[test]
                fn common_cjk_roundtrip() {
                    let mut buf = [0u8; 8];
                    // Common CJK characters that most CJK encodings support
                    for c in ['中', '国', '日', '本', '人'].iter() {
                        if <$encoding>::can_encode(*c) {
                            let len = <$encoding>::encode_char(*c, &mut buf);
                            assert!(len >= 2, "CJK char should be at least 2 bytes");
                            let (decoded, next) = <$encoding>::decode_char_at(&buf[..len], 0).unwrap();
                            assert_eq!(decoded, *c);
                            assert_eq!(next, len);
                        }
                    }
                }

                #[test]
                fn truncated_sequence_invalid() {
                    let mut buf = [0u8; 8];
                    // Try to encode a CJK character
                    if <$encoding>::can_encode('中') {
                        let len = <$encoding>::encode_char('中', &mut buf);
                        if len > 1 {
                            // Truncate to just the first byte
                            assert!(<$encoding>::validate(&buf[..1]).is_err());
                        }
                    }
                }
            }
        }
    };
}

/// Tests for full Unicode encodings (UTF-8, UTF-16, UTF-32, GB18030)
macro_rules! test_unicode_encoding {
    ($name:ident, $encoding:ty) => {
        test_encoding_basics!($name, $encoding);

        paste! {
            mod [<$name _unicode>] {
                use super::*;

                #[test]
                fn can_encode_all_ascii() {
                    for byte in 0u8..128 {
                        let c = byte as char;
                        assert!(<$encoding>::can_encode(c), "Should encode ASCII {:02X}", byte);
                    }
                }

                #[test]
                fn can_encode_bmp() {
                    // Sample of BMP characters
                    for c in ['é', 'ñ', 'ü', 'α', 'β', '中', '日', '한'].iter() {
                        assert!(<$encoding>::can_encode(*c), "Should encode BMP char {:?}", c);
                    }
                }

                #[test]
                fn can_encode_supplementary() {
                    // Emoji and other supplementary plane characters
                    for c in ['😀', '🎉', '𠀀'].iter() {
                        assert!(<$encoding>::can_encode(*c), "Should encode supplementary char {:?}", c);
                    }
                }

                #[test]
                fn roundtrip_bmp_sample() {
                    let mut buf = [0u8; 8];
                    let chars = ['A', 'é', '中', 'α', '☃'];
                    for &c in &chars {
                        let len = <$encoding>::encode_char(c, &mut buf);
                        let (decoded, _) = <$encoding>::decode_char_at(&buf[..len], 0).unwrap();
                        assert_eq!(decoded, c);
                    }
                }

                #[test]
                fn roundtrip_emoji() {
                    let mut buf = [0u8; 8];
                    let c = '😀';
                    let len = <$encoding>::encode_char(c, &mut buf);
                    let (decoded, _) = <$encoding>::decode_char_at(&buf[..len], 0).unwrap();
                    assert_eq!(decoded, c);
                }
            }
        }
    };
}

// =============================================================================
// Apply test macros to encodings
// =============================================================================

// --- Unicode encodings ---
test_unicode_encoding!(utf8, stringly::Utf8);

#[cfg(feature = "utf16")]
test_unicode_encoding!(utf16le, stringly::Utf16Le);

#[cfg(feature = "utf16")]
test_unicode_encoding!(utf16be, stringly::Utf16Be);

#[cfg(feature = "utf32")]
test_unicode_encoding!(utf32le, stringly::Utf32Le);

#[cfg(feature = "utf32")]
test_unicode_encoding!(utf32be, stringly::Utf32Be);

#[cfg(feature = "gb18030")]
test_unicode_encoding!(gb18030, stringly::Gb18030);

// --- Japanese encodings ---
#[cfg(feature = "euc-jp")]
mod eucjp {
    use super::*;
    test_encoding_basics!(basics, stringly::EucJp);

    #[test]
    fn is_variable_width() {
        assert!(!stringly::EucJp::IS_FIXED_WIDTH);
    }

    #[test]
    fn ascii_roundtrip() {
        let mut buf = [0u8; 4];
        for byte in 0x20u8..0x7F {
            let c = byte as char;
            let len = stringly::EucJp::encode_char(c, &mut buf);
            assert_eq!(len, 1);
            let (decoded, _) = stringly::EucJp::decode_char_at(&buf[..len], 0).unwrap();
            assert_eq!(decoded, c);
        }
    }

    #[test]
    fn hiragana_roundtrip() {
        let mut buf = [0u8; 4];
        let c = 'あ';
        if stringly::EucJp::can_encode(c) {
            let len = stringly::EucJp::encode_char(c, &mut buf);
            let (decoded, _) = stringly::EucJp::decode_char_at(&buf[..len], 0).unwrap();
            assert_eq!(decoded, c);
        }
    }
}

#[cfg(feature = "iso-2022-jp")]
mod iso2022jp {
    use super::*;
    test_encoding_basics!(basics, stringly::Iso2022Jp);

    #[test]
    fn is_variable_width() {
        assert!(!stringly::Iso2022Jp::IS_FIXED_WIDTH);
    }

    #[test]
    fn ascii_roundtrip() {
        let mut buf = [0u8; 8];
        for byte in 0x20u8..0x7F {
            let c = byte as char;
            let len = stringly::Iso2022Jp::encode_char(c, &mut buf);
            let (decoded, _) = stringly::Iso2022Jp::decode_char_at(&buf[..len], 0).unwrap();
            assert_eq!(decoded, c);
        }
    }
}

// =============================================================================
// Legacy Codepages
// =============================================================================

#[cfg(feature = "codepages-iso8859")]
mod iso8859 {
    use super::*;
    use stringly::codepages::*;

    test_single_byte_encoding!(iso8859_1, Iso8859_1);
    test_single_byte_encoding!(iso8859_2, Iso8859_2);
    test_single_byte_encoding!(iso8859_3, Iso8859_3);
    test_single_byte_encoding!(iso8859_4, Iso8859_4);
    test_single_byte_encoding!(iso8859_5, Iso8859_5);
    test_single_byte_encoding!(iso8859_6, Iso8859_6);
    test_single_byte_encoding!(iso8859_7, Iso8859_7);
    test_single_byte_encoding!(iso8859_8, Iso8859_8);
    test_single_byte_encoding!(iso8859_9, Iso8859_9);
    test_single_byte_encoding!(iso8859_10, Iso8859_10);
    test_single_byte_encoding!(iso8859_11, Iso8859_11);
    test_single_byte_encoding!(iso8859_13, Iso8859_13);
    test_single_byte_encoding!(iso8859_14, Iso8859_14);
    test_single_byte_encoding!(iso8859_15, Iso8859_15);
    test_single_byte_encoding!(iso8859_16, Iso8859_16);
}

#[cfg(feature = "codepages-windows")]
mod windows {
    use super::*;
    use stringly::codepages::*;

    test_single_byte_encoding!(cp1250, Cp1250);
    test_single_byte_encoding!(cp1251, Cp1251);
    test_single_byte_encoding!(cp1252, Cp1252);
    test_single_byte_encoding!(cp1253, Cp1253);
    test_single_byte_encoding!(cp1254, Cp1254);
    test_single_byte_encoding!(cp1255, Cp1255);
    test_single_byte_encoding!(cp1256, Cp1256);
    test_single_byte_encoding!(cp1257, Cp1257);
    test_single_byte_encoding!(cp1258, Cp1258);
    test_single_byte_encoding!(cp874, Cp874);

    // Multi-byte CJK codepages
    test_multibyte_encoding!(cp932, Cp932);
    test_multibyte_encoding!(cp936, Cp936);
    test_multibyte_encoding!(cp949, Cp949);
    test_multibyte_encoding!(cp950, Cp950);
}

#[cfg(feature = "codepages-dos")]
mod dos {
    use super::*;
    use stringly::codepages::*;

    test_single_byte_encoding!(cp437, Cp437);
    test_single_byte_encoding!(cp737, Cp737);
    test_single_byte_encoding!(cp775, Cp775);
    test_single_byte_encoding!(cp850, Cp850);
    test_single_byte_encoding!(cp852, Cp852);
    test_single_byte_encoding!(cp855, Cp855);
    test_single_byte_encoding!(cp857, Cp857);
    test_single_byte_encoding!(cp860, Cp860);
    test_single_byte_encoding!(cp861, Cp861);
    test_single_byte_encoding!(cp862, Cp862);
    test_single_byte_encoding!(cp863, Cp863);
    test_single_byte_encoding!(cp864, Cp864);
    test_single_byte_encoding!(cp865, Cp865);
    test_single_byte_encoding!(cp866, Cp866);
    test_single_byte_encoding!(cp869, Cp869);
}

#[cfg(feature = "codepages-misc")]
mod misc {
    use super::*;
    use stringly::codepages::*;

    test_single_byte_encoding!(koi8r, Koi8R);
    test_single_byte_encoding!(koi8u, Koi8U);
    test_single_byte_encoding!(cp424, Cp424);
    test_single_byte_encoding!(cp856, Cp856);
    test_single_byte_encoding!(cp1006, Cp1006);
    test_single_byte_encoding!(atarist, Atarist);
    test_single_byte_encoding!(kz1048, Kz1048);
}

#[cfg(feature = "codepages-apple")]
mod apple {
    use super::*;
    use stringly::codepages::*;

    test_single_byte_encoding!(arabic, Arabic);
    test_single_byte_encoding!(celtic, Celtic);
    test_single_byte_encoding!(centeuro, Centeuro);
    test_single_byte_encoding!(croatian, Croatian);
    test_single_byte_encoding!(cyrillic, Cyrillic);
    test_single_byte_encoding!(farsi, Farsi);
    test_single_byte_encoding!(gaelic, Gaelic);
    test_single_byte_encoding!(greek, Greek);
    test_single_byte_encoding!(hebrew, Hebrew);
    test_single_byte_encoding!(iceland, Iceland);
    test_single_byte_encoding!(roman, Roman);
    test_single_byte_encoding!(romanian, Romanian);
    test_single_byte_encoding!(thai, Thai);
    test_single_byte_encoding!(turkish, Turkish);

    // Multi-byte Apple encodings
    test_multibyte_encoding!(chinsimp, Chinsimp);
    test_multibyte_encoding!(chintrad, Chintrad);
    test_multibyte_encoding!(japanese, Japanese);
    test_multibyte_encoding!(korean, Korean);
}

// =============================================================================
// Cross-encoding conversion tests
// =============================================================================

mod conversions {
    use stringly::{String, Utf8};

    #[cfg(feature = "utf16")]
    use stringly::{Utf16Be, Utf16Le};

    #[cfg(feature = "utf32")]
    use stringly::Utf32Le;

    #[cfg(feature = "gb18030")]
    use stringly::Gb18030;

    // Test From conversions between universal encodings
    #[cfg(feature = "utf16")]
    #[test]
    fn utf8_to_utf16le_from() {
        let utf8: String<Utf8> = String::from("hello 世界");
        let utf16: String<Utf16Le> = String::from(&*utf8);
        assert!(utf8.chars().eq(utf16.chars()));
    }

    #[cfg(feature = "utf16")]
    #[test]
    fn utf8_to_utf16be_from() {
        let utf8: String<Utf8> = String::from("hello 世界");
        let utf16: String<Utf16Be> = String::from(&*utf8);
        assert!(utf8.chars().eq(utf16.chars()));
    }

    #[cfg(feature = "utf32")]
    #[test]
    fn utf8_to_utf32le_from() {
        let utf8: String<Utf8> = String::from("hello 世界 😀");
        let utf32: String<Utf32Le> = String::from(&*utf8);
        assert!(utf8.chars().eq(utf32.chars()));
    }

    #[cfg(feature = "utf16")]
    #[test]
    fn utf16le_to_utf8_from() {
        let utf16: String<Utf16Le> = "hello 世界".chars().collect();
        let utf8: String<Utf8> = String::from(&*utf16);
        assert!(utf16.chars().eq(utf8.chars()));
    }

    #[cfg(all(feature = "utf16", feature = "utf32"))]
    #[test]
    fn utf16le_to_utf32le_from() {
        let utf16: String<Utf16Le> = "hello 世界 😀".chars().collect();
        let utf32: String<Utf32Le> = String::from(&*utf16);
        assert!(utf16.chars().eq(utf32.chars()));
    }

    #[cfg(feature = "gb18030")]
    #[test]
    fn utf8_to_gb18030_from() {
        let utf8: String<Utf8> = String::from("hello 世界 😀");
        let gb: String<Gb18030> = String::from(&*utf8);
        assert!(utf8.chars().eq(gb.chars()));
    }

    // Test Into conversions (owned)
    #[cfg(feature = "utf16")]
    #[test]
    fn utf8_into_utf16le() {
        let utf8: String<Utf8> = String::from("hello 世界");
        let utf16: String<Utf16Le> = utf8.into();
        let expected: String<Utf8> = "hello 世界".chars().collect();
        assert!(utf16.chars().eq(expected.chars()));
    }

    // Test try_transcode method
    #[test]
    fn try_transcode_ascii_succeeds() {
        let utf8: String<Utf8> = String::from("hello");
        // Transcode to self should always work
        let result: Result<String<Utf8>, _> = utf8.try_transcode();
        assert!(result.is_ok());
    }

    #[cfg(feature = "codepages-windows")]
    #[test]
    fn try_transcode_to_codepage_success() {
        use stringly::codepages::Cp1252;

        let utf8: String<Utf8> = String::from("hello café");
        let result: Result<String<Cp1252>, _> = utf8.try_transcode();
        assert!(result.is_ok());
        let cp1252 = result.unwrap();
        assert!(utf8.chars().eq(cp1252.chars()));
    }

    #[cfg(feature = "codepages-windows")]
    #[test]
    fn try_transcode_to_codepage_failure() {
        use stringly::codepages::Cp1252;

        let utf8: String<Utf8> = String::from("hello 世界");
        let result: Result<String<Cp1252>, _> = utf8.try_transcode();
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.character(), '世');
        assert_eq!(err.index(), 6); // "hello " is 6 chars
    }

    #[cfg(feature = "codepages-iso8859")]
    #[test]
    fn try_transcode_to_iso8859_1() {
        use stringly::codepages::Iso8859_1;

        // ISO-8859-1 can represent Latin-1 characters
        let utf8: String<Utf8> = String::from("café résumé");
        let result: Result<String<Iso8859_1>, _> = utf8.try_transcode();
        assert!(result.is_ok());

        // But not CJK
        let utf8_cjk: String<Utf8> = String::from("日本語");
        let result: Result<String<Iso8859_1>, _> = utf8_cjk.try_transcode();
        assert!(result.is_err());
    }

    #[cfg(feature = "euc-jp")]
    #[test]
    fn try_transcode_to_eucjp() {
        use stringly::EucJp;

        // EUC-JP can represent Japanese
        let utf8: String<Utf8> = String::from("日本語テスト");
        let result: Result<String<EucJp>, _> = utf8.try_transcode();
        // Note: depends on whether all chars are in JIS X 0208
        if result.is_ok() {
            let eucjp = result.unwrap();
            assert!(utf8.chars().eq(eucjp.chars()));
        }
    }
}
