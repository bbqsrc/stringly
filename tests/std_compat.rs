//! Tests ported from the Rust standard library for String and str.
//!
//! These tests verify that `Str<E>` and `String<E>` behave consistently
//! with std's `str` and `String` types.

use stringly::{Str, String, Utf8};

type Utf8Str = Str<Utf8>;
type Utf8String = String<Utf8>;

// Helper to create a Utf8String from &str
fn s(x: &str) -> Utf8String {
    Utf8String::from(x)
}

// Helper to create a &Utf8Str from &str
fn st(x: &str) -> &Utf8Str {
    Utf8Str::from_bytes(x.as_bytes()).unwrap()
}

// Helper to convert Str<E> to std::string::String for comparison
fn to_std(s: &Utf8Str) -> std::string::String {
    s.chars().collect()
}

// =============================================================================
// String construction and capacity tests
// =============================================================================

mod string_construction {
    use super::*;

    #[test]
    fn test_new() {
        let s = Utf8String::new();
        assert_eq!(s.len(), 0);
        assert!(s.is_empty());
    }

    #[test]
    fn test_with_capacity() {
        let s = Utf8String::with_capacity(10);
        assert!(s.capacity() >= 10);
        assert!(s.is_empty());
    }

    #[test]
    fn test_from_bytes() {
        let bytes = b"hello".to_vec();
        let s = Utf8String::from_bytes(bytes).unwrap();
        assert_eq!(s.len(), 5);

        let invalid = b"hello\xFF".to_vec();
        assert!(Utf8String::from_bytes(invalid).is_err());
    }

    #[test]
    fn test_from_bytes_lossy() {
        let valid = b"hello";
        let s: Utf8String = Utf8String::from_bytes_lossy(valid);
        assert_eq!(to_std(&s), "hello");

        let invalid = b"hello\xFFworld";
        let s: Utf8String = Utf8String::from_bytes_lossy(invalid);
        assert_eq!(to_std(&s), "hello\u{FFFD}world");
    }
}

// =============================================================================
// String mutation tests
// =============================================================================

mod string_mutation {
    use super::*;

    #[test]
    fn test_push_str() {
        let mut s = Utf8String::new();
        s.push_str(st(""));
        assert_eq!(s.len(), 0);
        s.push_str(st("abc"));
        assert_eq!(s.len(), 3);
        s.push_str(st("ประเทศไทย中华Việt Nam"));
        assert_eq!(to_std(&s), "abcประเทศไทย中华Việt Nam");
    }

    #[test]
    fn test_push() {
        let mut data = s("ประเทศไทย中");
        data.push('华');
        data.push('b'); // 1 byte
        data.push('¢'); // 2 byte
        data.push('€'); // 3 byte
        data.push('𤭢'); // 4 byte
        assert_eq!(to_std(&data), "ประเทศไทย中华b¢€𤭢");
    }

    #[test]
    fn test_pop() {
        let mut data = s("ประเทศไทย中华b¢€𤭢");
        assert_eq!(data.pop().unwrap(), '𤭢'); // 4 bytes
        assert_eq!(data.pop().unwrap(), '€'); // 3 bytes
        assert_eq!(data.pop().unwrap(), '¢'); // 2 bytes
        assert_eq!(data.pop().unwrap(), 'b'); // 1 byte
        assert_eq!(data.pop().unwrap(), '华');
        assert_eq!(to_std(&data), "ประเทศไทย中");
    }

    #[test]
    fn test_truncate() {
        let mut s = Utf8String::from("12345");
        s.truncate(5);
        assert_eq!(to_std(&s), "12345");
        s.truncate(3);
        assert_eq!(to_std(&s), "123");
        s.truncate(0);
        assert_eq!(to_std(&s), "");
    }

    #[test]
    fn test_truncate_invalid_len() {
        let mut s = Utf8String::from("12345");
        s.truncate(6);
        assert_eq!(to_std(&s), "12345");
    }

    #[test]
    #[should_panic]
    fn test_truncate_split_codepoint() {
        let mut s = Utf8String::from("\u{FC}"); // ü
        s.truncate(1);
    }

    #[test]
    fn test_clear() {
        let mut s = Utf8String::from("12345");
        s.clear();
        assert_eq!(s.len(), 0);
        assert!(s.is_empty());
    }

    #[test]
    fn test_insert() {
        let mut s = s("foobar");
        s.insert(0, 'ệ');
        assert_eq!(to_std(&s), "ệfoobar");
        s.insert(6, 'ย');
        assert_eq!(to_std(&s), "ệfooยbar");
    }

    #[test]
    #[should_panic]
    fn test_insert_bad1() {
        s("").insert(1, 't');
    }

    #[test]
    #[should_panic]
    fn test_insert_bad2() {
        s("ệ").insert(1, 't');
    }

    #[test]
    fn test_remove() {
        let mut s = s("ศไทย中华Việt Nam; foobar");
        assert_eq!(s.remove(0), 'ศ');
        assert_eq!(s.len(), 33);
        assert_eq!(to_std(&s), "ไทย中华Việt Nam; foobar");
        assert_eq!(s.remove(17), 'ệ');
        assert_eq!(to_std(&s), "ไทย中华Vit Nam; foobar");
    }

    #[test]
    #[should_panic]
    fn test_remove_bad() {
        s("ศ").remove(1);
    }

    #[test]
    fn test_insert_str() {
        let mut s = s("foobar");
        s.insert_str(0, st("hello "));
        assert_eq!(to_std(&s), "hello foobar");
        s.insert_str(6, st("world "));
        assert_eq!(to_std(&s), "hello world foobar");
    }

    #[test]
    fn test_reserve() {
        let mut s = Utf8String::new();
        assert_eq!(s.capacity(), 0);
        s.reserve(2);
        assert!(s.capacity() >= 2);
        for _ in 0..16 {
            s.push('0');
        }
        assert!(s.capacity() >= 16);
        s.reserve(16);
        assert!(s.capacity() >= 32);
    }
}

// =============================================================================
// Str basic operations tests
// =============================================================================

mod str_basics {
    use super::*;

    #[test]
    fn test_len() {
        let s = st("hello");
        assert_eq!(s.len(), 5);

        let s = st("ศไทย中华Việt Nam");
        assert_eq!(s.len(), 28);
    }

    #[test]
    fn test_is_empty() {
        let s = st("");
        assert!(s.is_empty());

        let s = st("a");
        assert!(!s.is_empty());
    }

    #[test]
    fn test_is_char_boundary() {
        let s = st("ศไทย中华Việt Nam β-release 🐱123");
        assert!(s.is_char_boundary(0));
        assert!(s.is_char_boundary(s.len()));
        assert!(!s.is_char_boundary(s.len() + 1));

        for (i, ch) in s.char_indices() {
            assert!(s.is_char_boundary(i), "{} is a char boundary", i);
            for j in 1..ch.len_utf8() {
                assert!(
                    !s.is_char_boundary(i + j),
                    "{} should not be a char boundary",
                    i + j
                );
            }
        }
    }

    #[test]
    fn test_as_bytes() {
        let s = st("");
        assert_eq!(s.as_bytes(), b"");

        let s = st("abc");
        assert_eq!(s.as_bytes(), b"abc");

        let expected = [
            224, 184, 168, 224, 185, 132, 224, 184, 151, 224, 184, 162, 228, 184, 173, 229, 141,
            142, 86, 105, 225, 187, 135, 116, 32, 78, 97, 109,
        ];
        let s = st("ศไทย中华Việt Nam");
        assert_eq!(s.as_bytes(), expected);
    }
}

// =============================================================================
// Iterator tests
// =============================================================================

mod iterators {
    use super::*;

    #[test]
    fn test_chars() {
        let s = st("ศไทย中华Việt Nam");
        let v = [
            'ศ', 'ไ', 'ท', 'ย', '中', '华', 'V', 'i', 'ệ', 't', ' ', 'N', 'a', 'm',
        ];

        let mut pos = 0;
        for c in s.chars() {
            assert_eq!(c, v[pos]);
            pos += 1;
        }
        assert_eq!(pos, v.len());
        assert_eq!(s.chars().count(), v.len());
    }

    #[test]
    fn test_chars_rev() {
        let s = st("ศไทย中华Việt Nam");
        let v = [
            'm', 'a', 'N', ' ', 't', 'ệ', 'i', 'V', '华', '中', 'ย', 'ท', 'ไ', 'ศ',
        ];

        let mut pos = 0;
        for c in s.chars().rev() {
            assert_eq!(c, v[pos]);
            pos += 1;
        }
        assert_eq!(pos, v.len());
    }

    #[test]
    fn test_char_indices() {
        let s = st("ศไทย中华Việt Nam");
        let p = [0, 3, 6, 9, 12, 15, 18, 19, 20, 23, 24, 25, 26, 27];
        let v = [
            'ศ', 'ไ', 'ท', 'ย', '中', '华', 'V', 'i', 'ệ', 't', ' ', 'N', 'a', 'm',
        ];

        let mut pos = 0;
        for (idx, c) in s.char_indices() {
            assert_eq!((idx, c), (p[pos], v[pos]));
            pos += 1;
        }
        assert_eq!(pos, v.len());
    }

    #[test]
    fn test_char_indices_rev() {
        let s = st("ศไทย中华Việt Nam");
        let p = [27, 26, 25, 24, 23, 20, 19, 18, 15, 12, 9, 6, 3, 0];
        let v = [
            'm', 'a', 'N', ' ', 't', 'ệ', 'i', 'V', '华', '中', 'ย', 'ท', 'ไ', 'ศ',
        ];

        let mut pos = 0;
        for (idx, c) in s.char_indices().rev() {
            assert_eq!((idx, c), (p[pos], v[pos]));
            pos += 1;
        }
        assert_eq!(pos, v.len());
    }

    #[test]
    fn test_bytes() {
        let s = st("ศไทย中华Việt Nam");
        let v = [
            224, 184, 168, 224, 185, 132, 224, 184, 151, 224, 184, 162, 228, 184, 173, 229, 141,
            142, 86, 105, 225, 187, 135, 116, 32, 78, 97, 109,
        ];

        let mut pos = 0;
        for b in s.bytes() {
            assert_eq!(b, v[pos]);
            pos += 1;
        }
    }

    #[test]
    fn test_bytes_rev() {
        let s = st("ศไทย中华Việt Nam");
        let v = [
            224, 184, 168, 224, 185, 132, 224, 184, 151, 224, 184, 162, 228, 184, 173, 229, 141,
            142, 86, 105, 225, 187, 135, 116, 32, 78, 97, 109,
        ];

        let mut pos = v.len();
        for b in s.bytes().rev() {
            pos -= 1;
            assert_eq!(b, v[pos]);
        }
    }

    #[test]
    fn test_lines() {
        let s = st("hello\nworld\n");
        let lines: Vec<_> = s.lines().map(|l| to_std(l)).collect();
        assert_eq!(lines, vec!["hello", "world"]);

        let s = st("hello\r\nworld\r\n");
        let lines: Vec<_> = s.lines().map(|l| to_std(l)).collect();
        assert_eq!(lines, vec!["hello", "world"]);

        let s = st("hello\nworld");
        let lines: Vec<_> = s.lines().map(|l| to_std(l)).collect();
        assert_eq!(lines, vec!["hello", "world"]);
    }
}

// =============================================================================
// Searching tests (using char patterns which are supported)
// =============================================================================

mod searching {
    use super::*;

    #[test]
    fn test_find_char() {
        let s = st("hello");
        assert_eq!(s.find('l'), Some(2));
        assert_eq!(s.find('x'), None);

        let s = st("ประเทศไทย中华Việt Nam");
        assert_eq!(s.find('华'), Some(30));
    }

    #[test]
    fn test_find_closure() {
        let s = st("hello");
        assert_eq!(s.find(|c: char| c == 'o'), Some(4));
        assert_eq!(s.find(|c: char| c == 'x'), None);

        let s = st("ประเทศไทย中华Việt Nam");
        assert_eq!(s.find(|c: char| c == '华'), Some(30));
    }

    #[test]
    fn test_rfind_char() {
        let s = st("hello");
        assert_eq!(s.rfind('l'), Some(3));
        assert_eq!(s.rfind('x'), None);

        let s = st("ประเทศไทย中华Việt Nam");
        assert_eq!(s.rfind('华'), Some(30));
    }

    #[test]
    fn test_rfind_closure() {
        let s = st("hello");
        assert_eq!(s.rfind(|c: char| c == 'o'), Some(4));
        assert_eq!(s.rfind(|c: char| c == 'x'), None);
    }

    #[test]
    fn test_find_str_pattern() {
        let s = st("abcabc");
        // Use Str<E> pattern
        assert_eq!(s.find(st("ab")), Some(0));
        assert_eq!(s.find(st("bc")), Some(1));
        assert_eq!(s.find(st("xyz")), None);
    }

    #[test]
    fn test_contains_char() {
        let s = st("abc");
        assert!(s.contains('b'));
        assert!(s.contains('a'));
        assert!(!s.contains('d'));

        let s = st("");
        assert!(!s.contains('a'));
    }

    #[test]
    fn test_contains_str() {
        let s = st("abcde");
        assert!(s.contains(st("bcd")));
        assert!(s.contains(st("abcd")));
        assert!(s.contains(st("bcde")));
        assert!(!s.contains(st("def")));

        let s = st("ประเทศไทย中华Việt Nam");
        assert!(s.contains(st("中华")));
        assert!(!s.contains(st("ไท华")));
    }

    #[test]
    fn test_starts_with_char() {
        let s = st("abc");
        assert!(s.starts_with('a'));
        assert!(!s.starts_with('b'));
    }

    #[test]
    fn test_starts_with_str() {
        let s = st("");
        assert!(s.starts_with(st("")));

        let s = st("abc");
        assert!(s.starts_with(st("")));
        assert!(s.starts_with(st("a")));
        assert!(s.starts_with(st("ab")));
        assert!(!s.starts_with(st("b")));

        let s = st("ödd");
        assert!(s.starts_with(st("öd")));
    }

    #[test]
    fn test_ends_with_char() {
        let s = st("abc");
        assert!(s.ends_with('c'));
        assert!(!s.ends_with('b'));
    }

    #[test]
    fn test_ends_with_str() {
        let s = st("");
        assert!(s.ends_with(st("")));

        let s = st("abc");
        assert!(s.ends_with(st("")));
        assert!(s.ends_with(st("c")));
        assert!(s.ends_with(st("bc")));
        assert!(!s.ends_with(st("b")));

        let s = st("ddö");
        assert!(s.ends_with(st("dö")));
    }
}

// =============================================================================
// Splitting tests
// =============================================================================

mod splitting {
    use super::*;

    #[test]
    fn test_split_char() {
        let s = st("a-b-c");
        let parts: Vec<_> = s.split('-').map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["a", "b", "c"]);
    }

    #[test]
    fn test_split_str() {
        let s = st("a--b--c");
        let parts: Vec<_> = s.split(st("--")).map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["a", "b", "c"]);
    }

    #[test]
    fn test_split_closure() {
        let s = st("a1b2c3");
        let parts: Vec<_> = s
            .split(|c: char| c.is_numeric())
            .map(|p| to_std(p))
            .collect();
        assert_eq!(parts, vec!["a", "b", "c", ""]);
    }

    #[test]
    fn test_splitn() {
        let data = st("\nMäry häd ä little lämb\nLittle lämb\n");
        let split: Vec<_> = data.splitn(4, ' ').map(|p| to_std(p)).collect();
        assert_eq!(split, ["\nMäry", "häd", "ä", "little lämb\nLittle lämb\n"]);
    }

    #[test]
    fn test_rsplit() {
        let data = st("\nMäry häd ä little lämb\nLittle lämb\n");
        let split: Vec<_> = data.rsplit(' ').map(|p| to_std(p)).collect();
        assert_eq!(
            split,
            ["lämb\n", "lämb\nLittle", "little", "ä", "häd", "\nMäry"]
        );
    }

    #[test]
    fn test_rsplitn() {
        let data = st("\nMäry häd ä little lämb\nLittle lämb\n");
        let split: Vec<_> = data.rsplitn(2, ' ').map(|p| to_std(p)).collect();
        assert_eq!(split, ["lämb\n", "\nMäry häd ä little lämb\nLittle"]);
    }

    #[test]
    fn test_split_terminator() {
        let data = st("\nMäry häd ä little lämb\nLittle lämb\n");
        let split: Vec<_> = data.split('\n').map(|p| to_std(p)).collect();
        assert_eq!(split, ["", "Märy häd ä little lämb", "Little lämb", ""]);

        let split: Vec<_> = data.split_terminator('\n').map(|p| to_std(p)).collect();
        assert_eq!(split, ["", "Märy häd ä little lämb", "Little lämb"]);
    }

    #[test]
    fn test_split_inclusive() {
        let data = st("\nMäry häd ä little lämb\nLittle lämb\n");
        let split: Vec<_> = data.split_inclusive('\n').map(|p| to_std(p)).collect();
        assert_eq!(split, ["\n", "Märy häd ä little lämb\n", "Little lämb\n"]);
    }

    #[test]
    fn test_split_whitespace() {
        let s = st("  hello   world  ");
        let parts: Vec<_> = s.split_whitespace().map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["hello", "world"]);
    }

    #[test]
    fn test_split_ascii_whitespace() {
        let s = st("  hello   world  ");
        // split_ascii_whitespace returns &[u8], so convert via core::str::from_utf8
        let parts: Vec<_> = s
            .split_ascii_whitespace()
            .map(|p| core::str::from_utf8(p).unwrap().to_string())
            .collect();
        assert_eq!(parts, vec!["hello", "world"]);
    }

    #[test]
    fn test_split_at() {
        let s = st("ศไทย中华Việt Nam");
        for (index, _) in s.char_indices() {
            let (a, b) = s.split_at(index);
            assert_eq!(a.len() + b.len(), s.len());
        }
        let (a, b) = s.split_at(s.len());
        assert_eq!(a.len(), s.len());
        assert_eq!(b.len(), 0);
    }

    #[test]
    #[should_panic]
    fn test_split_at_boundscheck() {
        let s = st("ศไทย中华Việt Nam");
        let _ = s.split_at(1); // Not a char boundary
    }

    #[test]
    fn test_split_once() {
        let s = st("");
        assert!(s.split_once(st("->")).is_none());

        let s = st("a->b");
        let (left, right) = s.split_once(st("->")).unwrap();
        assert_eq!(to_std(left), "a");
        assert_eq!(to_std(right), "b");

        let s = st("a->b->c");
        let (left, right) = s.split_once(st("->")).unwrap();
        assert_eq!(to_std(left), "a");
        assert_eq!(to_std(right), "b->c");
    }

    #[test]
    fn test_rsplit_once() {
        let s = st("");
        assert!(s.rsplit_once(st("->")).is_none());

        let s = st("a->b");
        let (left, right) = s.rsplit_once(st("->")).unwrap();
        assert_eq!(to_std(left), "a");
        assert_eq!(to_std(right), "b");

        let s = st("a->b->c");
        let (left, right) = s.rsplit_once(st("->")).unwrap();
        assert_eq!(to_std(left), "a->b");
        assert_eq!(to_std(right), "c");
    }
}

// =============================================================================
// Trimming tests
// =============================================================================

mod trimming {
    use super::*;

    #[test]
    fn test_trim() {
        let cases = [
            ("", ""),
            ("a", "a"),
            ("    ", ""),
            ("    blah     ", "blah"),
            ("\nwut   \u{3000}  ", "wut"),
            (" hey dude ", "hey dude"),
        ];
        for (input, expected) in cases {
            let s = st(input);
            assert_eq!(to_std(s.trim()), expected);
        }
    }

    #[test]
    fn test_trim_start() {
        let cases = [
            ("", ""),
            ("a", "a"),
            ("    ", ""),
            ("     blah", "blah"),
            ("   \u{3000}  wut", "wut"),
            ("hey ", "hey "),
        ];
        for (input, expected) in cases {
            let s = st(input);
            assert_eq!(to_std(s.trim_start()), expected);
        }
    }

    #[test]
    fn test_trim_end() {
        let cases = [
            ("", ""),
            ("a", "a"),
            ("    ", ""),
            ("blah     ", "blah"),
            ("wut   \u{3000}  ", "wut"),
            (" hey", " hey"),
        ];
        for (input, expected) in cases {
            let s = st(input);
            assert_eq!(to_std(s.trim_end()), expected);
        }
    }

    #[test]
    fn test_trim_matches() {
        let s = st(" *** foo *** ");
        let chars: &[char] = &['*', ' '];
        assert_eq!(to_std(s.trim_matches(chars)), "foo");

        let s = st("11foo1bar11");
        assert_eq!(to_std(s.trim_matches('1')), "foo1bar");
    }

    #[test]
    fn test_trim_start_matches() {
        let s = st(" *** foo *** ");
        let chars: &[char] = &['*', ' '];
        assert_eq!(to_std(s.trim_start_matches(chars)), "foo *** ");

        let s = st("11foo1bar11");
        assert_eq!(to_std(s.trim_start_matches('1')), "foo1bar11");
    }

    #[test]
    fn test_trim_end_matches() {
        let s = st(" *** foo *** ");
        let chars: &[char] = &['*', ' '];
        assert_eq!(to_std(s.trim_end_matches(chars)), " *** foo");

        let s = st("11foo1bar11");
        assert_eq!(to_std(s.trim_end_matches('1')), "11foo1bar");
    }

    #[test]
    fn test_strip_prefix() {
        let s = st("hello world");
        assert_eq!(
            s.strip_prefix(st("hello ")).map(|s| to_std(s)),
            Some("world".to_string())
        );
        assert!(s.strip_prefix(st("world")).is_none());
    }

    #[test]
    fn test_strip_suffix() {
        let s = st("hello world");
        assert_eq!(
            s.strip_suffix(st(" world")).map(|s| to_std(s)),
            Some("hello".to_string())
        );
        assert!(s.strip_suffix(st("hello")).is_none());
    }
}

// =============================================================================
// Replace tests
// =============================================================================

mod replace {
    use super::*;

    // Note: stringly's replace() only supports char patterns, not &Str<E> patterns.
    // Tests for string patterns are omitted.

    #[test]
    fn test_replace_char() {
        let input = st("");
        assert_eq!(to_std(&input.replace('a', st("b"))), "");

        let input = st("a");
        assert_eq!(to_std(&input.replace('a', st("b"))), "b");

        let input = st("ab");
        assert_eq!(to_std(&input.replace('a', st("b"))), "bb");

        let input = st("aaaa");
        assert_eq!(to_std(&input.replace('a', st("b"))), "bbbb");
    }

    #[test]
    fn test_replace_unicode() {
        let data = st("ประเทศไทย中华");
        // Replace 'ป' (first character) with Arabic text
        assert_eq!(to_std(&data.replace('ป', st("X"))), "Xระเทศไทย中华");
    }

    #[test]
    fn test_replacen_char() {
        let input = st("");
        assert_eq!(to_std(&input.replacen('a', st("b"), 5)), "");

        let input = st("acaaa");
        assert_eq!(to_std(&input.replacen('a', st("b"), 3)), "bcbba");

        let input = st("aaaa");
        assert_eq!(to_std(&input.replacen('a', st("b"), 0)), "aaaa");
    }
}

// =============================================================================
// Indexing tests
// =============================================================================

mod indexing {
    use super::*;

    #[test]
    fn test_get() {
        let s = st("hello");
        assert_eq!(s.get(0..2).map(|s| to_std(s)), Some("he".to_string()));
        assert_eq!(s.get(2..5).map(|s| to_std(s)), Some("llo".to_string()));
        assert!(s.get(0..10).is_none());
    }

    #[test]
    fn test_get_unicode() {
        let s = st("日本");
        assert_eq!(s.get(0..3).map(|s| to_std(s)), Some("日".to_string()));
        assert!(s.get(0..2).is_none()); // Not a char boundary
        assert_eq!(s.get(3..6).map(|s| to_std(s)), Some("本".to_string()));
    }

    #[test]
    fn test_floor_char_boundary() {
        let s = st("❤️🧡💛💚💙💜");
        assert_eq!(s.floor_char_boundary(0), 0);
        assert_eq!(s.floor_char_boundary(1), 0);
        assert_eq!(s.floor_char_boundary(2), 0);
        assert_eq!(s.floor_char_boundary(3), 3);
        assert_eq!(s.floor_char_boundary(s.len()), s.len());
    }

    #[test]
    fn test_ceil_char_boundary() {
        let s = st("❤️🧡💛💚💙💜");
        assert_eq!(s.ceil_char_boundary(0), 0);
        assert_eq!(s.ceil_char_boundary(1), 3);
        assert_eq!(s.ceil_char_boundary(2), 3);
        assert_eq!(s.ceil_char_boundary(3), 3);
        assert_eq!(s.ceil_char_boundary(s.len()), s.len());
    }
}

// =============================================================================
// Drain tests
// =============================================================================

mod drain {
    use super::*;

    #[test]
    fn test_drain() {
        let mut str1 = s("αβγ");
        assert_eq!(str1.drain(2..4).collect::<std::string::String>(), "β");
        assert_eq!(to_std(&str1), "αγ");

        let mut str2 = s("abcd");
        str2.drain(..0);
        assert_eq!(to_std(&str2), "abcd");
        str2.drain(..1);
        assert_eq!(to_std(&str2), "bcd");
        str2.drain(3..);
        assert_eq!(to_std(&str2), "bcd");
        str2.drain(..);
        assert_eq!(to_std(&str2), "");
    }
}

// =============================================================================
// Escape tests
// =============================================================================

mod escape {
    use super::*;

    #[test]
    fn test_escape_unicode() {
        let s = st("abc");
        assert_eq!(s.escape_unicode().to_string(), "\\u{61}\\u{62}\\u{63}");

        let s = st("a c");
        assert_eq!(s.escape_unicode().to_string(), "\\u{61}\\u{20}\\u{63}");

        let s = st("\r\n\t");
        assert_eq!(s.escape_unicode().to_string(), "\\u{d}\\u{a}\\u{9}");
    }

    #[test]
    fn test_escape_debug() {
        let s = st("abc");
        assert_eq!(s.escape_debug().to_string(), "abc");

        let s = st("\0\r\n\t");
        assert_eq!(s.escape_debug().to_string(), "\\0\\r\\n\\t");

        let s = st("'\"\\");
        assert_eq!(s.escape_debug().to_string(), "\\'\\\"\\\\");
    }

    #[test]
    fn test_escape_default() {
        let s = st("abc");
        assert_eq!(s.escape_default().to_string(), "abc");

        let s = st("\r\n\t");
        assert_eq!(s.escape_default().to_string(), "\\r\\n\\t");
    }
}

// =============================================================================
// Match iterator tests
// =============================================================================

mod matches {
    use super::*;

    #[test]
    fn test_matches_char() {
        let s = st("abcabc");
        let matches: Vec<_> = s.matches('b').map(|m| to_std(m)).collect();
        assert_eq!(matches, vec!["b", "b"]);
    }

    #[test]
    fn test_matches_str() {
        let s = st("abcabc");
        let matches: Vec<_> = s.matches(st("bc")).map(|m| to_std(m)).collect();
        assert_eq!(matches, vec!["bc", "bc"]);
    }

    #[test]
    fn test_rmatches_char() {
        let s = st("abcabc");
        let matches: Vec<_> = s.rmatches('b').map(|m| to_std(m)).collect();
        assert_eq!(matches, vec!["b", "b"]);
    }

    #[test]
    fn test_match_indices_char() {
        let s = st("abcabc");
        let indices: Vec<_> = s.match_indices('b').map(|(i, m)| (i, to_std(m))).collect();
        assert_eq!(indices, vec![(1, "b".to_string()), (4, "b".to_string())]);
    }

    #[test]
    fn test_match_indices_str() {
        let s = st("abcabc");
        let indices: Vec<_> = s
            .match_indices(st("bc"))
            .map(|(i, m)| (i, to_std(m)))
            .collect();
        assert_eq!(indices, vec![(1, "bc".to_string()), (4, "bc".to_string())]);
    }

    #[test]
    fn test_rmatch_indices_char() {
        let s = st("abcabc");
        let indices: Vec<_> = s.rmatch_indices('b').map(|(i, m)| (i, to_std(m))).collect();
        assert_eq!(indices, vec![(4, "b".to_string()), (1, "b".to_string())]);
    }
}

// =============================================================================
// Comparison tests
// =============================================================================

mod comparison {
    use super::*;
    use std::cmp::Ordering::{Equal, Greater, Less};

    #[test]
    fn test_cmp() {
        let s1 = st("1234");
        let s2 = st("123");
        assert_eq!(s1.cmp(s2), Greater);

        let s1 = st("123");
        let s2 = st("1234");
        assert_eq!(s1.cmp(s2), Less);

        let s1 = st("1234");
        let s2 = st("1234");
        assert_eq!(s1.cmp(s2), Equal);
    }

    #[test]
    fn test_eq() {
        let s1 = st("hello");
        let s2 = st("hello");
        assert_eq!(s1, s2);

        let s3 = st("world");
        assert_ne!(s1, s3);
    }
}

// =============================================================================
// FromIterator tests
// =============================================================================

mod from_iterator {
    use super::*;

    #[test]
    fn test_collect_chars() {
        let s = st("ศไทย中华Việt Nam");
        let collected: Utf8String = s.chars().collect();
        assert_eq!(to_std(&collected), "ศไทย中华Việt Nam");
    }

    #[test]
    fn test_extend() {
        let mut s = s("hello");
        s.extend(" world".chars());
        assert_eq!(to_std(&s), "hello world");
    }
}

// =============================================================================
// String capacity management tests
// =============================================================================

mod string_capacity {
    use super::*;

    #[test]
    fn test_reserve_exact() {
        let mut s = Utf8String::new();
        s.reserve_exact(10);
        assert!(s.capacity() >= 10);

        // Reserve more
        s.reserve_exact(20);
        assert!(s.capacity() >= 20);
    }

    #[test]
    fn test_try_reserve() {
        let mut s = Utf8String::new();
        assert!(s.try_reserve(10).is_ok());
        assert!(s.capacity() >= 10);
    }

    #[test]
    fn test_try_reserve_exact() {
        let mut s = Utf8String::new();
        assert!(s.try_reserve_exact(10).is_ok());
        assert!(s.capacity() >= 10);
    }

    #[test]
    fn test_shrink_to_fit() {
        let mut s = Utf8String::with_capacity(100);
        s.push_str(st("hello"));
        assert!(s.capacity() >= 100);
        s.shrink_to_fit();
        assert!(s.capacity() < 100);
        assert!(s.capacity() >= 5);
    }

    #[test]
    fn test_shrink_to() {
        let mut s = Utf8String::with_capacity(100);
        s.push_str(st("hello"));
        s.shrink_to(10);
        assert!(s.capacity() >= 10);
        assert!(s.capacity() < 100);

        // Shrink to less than len should not truncate
        s.shrink_to(0);
        assert!(s.capacity() >= 5);
        assert_eq!(to_std(&s), "hello");
    }
}

// =============================================================================
// String range mutation tests
// =============================================================================

mod string_range_mutation {
    use super::*;

    #[test]
    fn test_split_off() {
        let mut s = s("hello world");
        let s2 = s.split_off(6);
        assert_eq!(to_std(&s), "hello ");
        assert_eq!(to_std(&s2), "world");
    }

    #[test]
    fn test_split_off_empty() {
        let mut s = s("hello");
        let s2 = s.split_off(0);
        assert_eq!(to_std(&s), "");
        assert_eq!(to_std(&s2), "hello");
    }

    #[test]
    fn test_split_off_end() {
        let mut s = s("hello");
        let s2 = s.split_off(5);
        assert_eq!(to_std(&s), "hello");
        assert_eq!(to_std(&s2), "");
    }

    #[test]
    fn test_split_off_unicode() {
        let mut s = s("日本語");
        let s2 = s.split_off(3); // After first character
        assert_eq!(to_std(&s), "日");
        assert_eq!(to_std(&s2), "本語");
    }

    #[test]
    #[should_panic]
    fn test_split_off_bad_boundary() {
        let mut s = s("日本語");
        let _ = s.split_off(1); // Not a char boundary
    }

    #[test]
    fn test_replace_range() {
        let mut s = s("hello world");
        s.replace_range(6..11, st("rust"));
        assert_eq!(to_std(&s), "hello rust");
    }

    #[test]
    fn test_replace_range_empty() {
        let mut s = s("hello");
        s.replace_range(2..2, st(" there "));
        assert_eq!(to_std(&s), "he there llo");
    }

    #[test]
    fn test_replace_range_full() {
        let mut s = s("hello");
        s.replace_range(.., st("world"));
        assert_eq!(to_std(&s), "world");
    }

    #[test]
    fn test_replace_range_unicode() {
        let mut s = s("日本語テスト");
        s.replace_range(3..9, st("中華")); // Replace 本語 with 中華
        assert_eq!(to_std(&s), "日中華テスト");
    }

    #[test]
    fn test_drain_full() {
        let mut s = s("hello");
        let drained: std::string::String = s.drain(..).collect();
        assert_eq!(drained, "hello");
        assert_eq!(to_std(&s), "");
    }

    #[test]
    fn test_drain_partial() {
        let mut s = s("hello world");
        let drained: std::string::String = s.drain(6..).collect();
        assert_eq!(drained, "world");
        assert_eq!(to_std(&s), "hello ");
    }

    #[test]
    fn test_drain_middle() {
        let mut s = s("hello world");
        let drained: std::string::String = s.drain(5..6).collect();
        assert_eq!(drained, " ");
        assert_eq!(to_std(&s), "helloworld");
    }

    #[test]
    fn test_drain_unicode() {
        let mut s = s("日本語");
        let drained: std::string::String = s.drain(3..6).collect();
        assert_eq!(drained, "本");
        assert_eq!(to_std(&s), "日語");
    }

    #[test]
    fn test_drain_drop_without_iterating() {
        let mut s = s("hello world");
        {
            let _ = s.drain(6..);
            // Drain dropped without iterating
        }
        assert_eq!(to_std(&s), "hello ");
    }
}

// =============================================================================
// String advanced mutation tests
// =============================================================================

mod string_advanced_mutation {
    use super::*;

    #[test]
    fn test_remove_matches_char() {
        let mut s = s("abcabc");
        s.remove_matches('a');
        assert_eq!(to_std(&s), "bcbc");
    }

    #[test]
    fn test_remove_matches_str() {
        let mut s = s("hello world world");
        s.remove_matches(st("world"));
        assert_eq!(to_std(&s), "hello  ");
    }

    #[test]
    fn test_remove_matches_none() {
        let mut s = s("hello");
        s.remove_matches('x');
        assert_eq!(to_std(&s), "hello");
    }

    #[test]
    fn test_remove_matches_unicode() {
        let mut s = s("日本日本");
        s.remove_matches('本');
        assert_eq!(to_std(&s), "日日");
    }

    #[test]
    fn test_retain() {
        let mut s = s("hello world");
        s.retain(|c| c != ' ');
        assert_eq!(to_std(&s), "helloworld");
    }

    #[test]
    fn test_retain_all() {
        let mut s = s("hello");
        s.retain(|_| true);
        assert_eq!(to_std(&s), "hello");
    }

    #[test]
    fn test_retain_none() {
        let mut s = s("hello");
        s.retain(|_| false);
        assert_eq!(to_std(&s), "");
    }

    #[test]
    fn test_retain_ascii_only() {
        let mut s = s("hello日本world");
        s.retain(|c| c.is_ascii());
        assert_eq!(to_std(&s), "helloworld");
    }

    #[test]
    fn test_retain_unicode() {
        let mut s = s("日本語テスト");
        s.retain(|c| c != '語');
        assert_eq!(to_std(&s), "日本テスト");
    }
}

// =============================================================================
// String operator tests
// =============================================================================

mod string_operators {
    use super::*;

    #[test]
    fn test_add() {
        let s1 = s("hello");
        let result = s1 + st(" world");
        assert_eq!(to_std(&result), "hello world");
    }

    #[test]
    fn test_add_empty() {
        let s1 = s("hello");
        let result = s1 + st("");
        assert_eq!(to_std(&result), "hello");
    }

    #[test]
    fn test_add_to_empty() {
        let s1 = s("");
        let result = s1 + st("hello");
        assert_eq!(to_std(&result), "hello");
    }

    #[test]
    fn test_add_unicode() {
        let s1 = s("日本");
        let result = s1 + st("語");
        assert_eq!(to_std(&result), "日本語");
    }

    #[test]
    fn test_add_assign() {
        let mut s1 = s("hello");
        s1 += st(" world");
        assert_eq!(to_std(&s1), "hello world");
    }

    #[test]
    fn test_add_assign_empty() {
        let mut s1 = s("hello");
        s1 += st("");
        assert_eq!(to_std(&s1), "hello");
    }

    #[test]
    fn test_index_range() {
        let s1 = s("hello world");
        let slice: &Utf8Str = &s1[0..5];
        assert_eq!(to_std(slice), "hello");
    }

    #[test]
    fn test_index_range_from() {
        let s1 = s("hello world");
        let slice: &Utf8Str = &s1[6..];
        assert_eq!(to_std(slice), "world");
    }

    #[test]
    fn test_index_range_to() {
        let s1 = s("hello world");
        let slice: &Utf8Str = &s1[..5];
        assert_eq!(to_std(slice), "hello");
    }

    #[test]
    fn test_index_range_full() {
        let s1 = s("hello");
        let slice: &Utf8Str = &s1[..];
        assert_eq!(to_std(slice), "hello");
    }

    #[test]
    fn test_index_mut() {
        let mut s1 = s("hello");
        let slice: &mut Utf8Str = &mut s1[..];
        assert_eq!(to_std(slice), "hello");
    }
}

// =============================================================================
// Str case conversion tests
// =============================================================================

mod str_case_conversion {
    use super::*;

    #[test]
    fn test_to_lowercase() {
        let s = st("HELLO");
        assert_eq!(to_std(&s.to_lowercase()), "hello");
    }

    #[test]
    fn test_to_lowercase_mixed() {
        let s = st("HeLLo WoRLD");
        assert_eq!(to_std(&s.to_lowercase()), "hello world");
    }

    #[test]
    fn test_to_lowercase_already_lower() {
        let s = st("hello");
        assert_eq!(to_std(&s.to_lowercase()), "hello");
    }

    #[test]
    fn test_to_lowercase_unicode() {
        let s = st("ÜBER");
        let lower = s.to_lowercase();
        assert_eq!(to_std(&lower), "über");
    }

    #[test]
    fn test_to_uppercase() {
        let s = st("hello");
        assert_eq!(to_std(&s.to_uppercase()), "HELLO");
    }

    #[test]
    fn test_to_uppercase_mixed() {
        let s = st("HeLLo WoRLD");
        assert_eq!(to_std(&s.to_uppercase()), "HELLO WORLD");
    }

    #[test]
    fn test_to_uppercase_already_upper() {
        let s = st("HELLO");
        assert_eq!(to_std(&s.to_uppercase()), "HELLO");
    }

    #[test]
    fn test_to_uppercase_unicode() {
        let s = st("über");
        let upper = s.to_uppercase();
        assert_eq!(to_std(&upper), "ÜBER");
    }

    #[test]
    fn test_to_ascii_lowercase() {
        let s = st("HELLO");
        assert_eq!(to_std(&s.to_ascii_lowercase()), "hello");
    }

    #[test]
    fn test_to_ascii_lowercase_unicode_unchanged() {
        let s = st("ÜBER");
        // Only ASCII characters are lowercased
        assert_eq!(to_std(&s.to_ascii_lowercase()), "Über");
    }

    #[test]
    fn test_to_ascii_uppercase() {
        let s = st("hello");
        assert_eq!(to_std(&s.to_ascii_uppercase()), "HELLO");
    }

    #[test]
    fn test_to_ascii_uppercase_unicode_unchanged() {
        let s = st("über");
        // Only ASCII characters are uppercased
        assert_eq!(to_std(&s.to_ascii_uppercase()), "üBER");
    }
}

// =============================================================================
// Str slicing edge case tests
// =============================================================================

mod str_slicing {
    use super::*;

    #[test]
    fn test_get_mut() {
        let mut s = s("hello");
        let slice = s.get_mut(0..2);
        assert!(slice.is_some());
        assert_eq!(to_std(slice.unwrap()), "he");
    }

    #[test]
    fn test_get_mut_invalid_boundary() {
        let mut s = s("日本語");
        let slice = s.get_mut(0..1); // Invalid boundary
        assert!(slice.is_none());
    }

    #[test]
    fn test_get_mut_out_of_bounds() {
        let mut s = s("hello");
        let slice = s.get_mut(0..10);
        assert!(slice.is_none());
    }

    #[test]
    fn test_split_at_mut() {
        let mut s = s("hello world");
        let (left, right) = s.split_at_mut(6);
        assert_eq!(to_std(left), "hello ");
        assert_eq!(to_std(right), "world");
    }

    #[test]
    fn test_split_at_mut_unicode() {
        let mut s = s("日本語");
        let (left, right) = s.split_at_mut(6); // After 日本
        assert_eq!(to_std(left), "日本");
        assert_eq!(to_std(right), "語");
    }

    #[test]
    fn test_split_at_mut_checked() {
        let mut s = s("hello");
        let result = s.split_at_mut_checked(3);
        assert!(result.is_some());
        let (left, right) = result.unwrap();
        assert_eq!(to_std(left), "hel");
        assert_eq!(to_std(right), "lo");
    }

    #[test]
    fn test_split_at_mut_checked_invalid() {
        let mut s = s("日本語");
        let result = s.split_at_mut_checked(1); // Invalid boundary
        assert!(result.is_none());
    }

    #[test]
    fn test_split_at_mut_checked_out_of_bounds() {
        let mut s = s("hello");
        let result = s.split_at_mut_checked(10);
        assert!(result.is_none());
    }
}

// =============================================================================
// Str repeat test
// =============================================================================

mod str_repeat {
    use super::*;

    #[test]
    fn test_repeat() {
        let s = st("ab");
        assert_eq!(to_std(&s.repeat(3)), "ababab");
    }

    #[test]
    fn test_repeat_zero() {
        let s = st("ab");
        assert_eq!(to_std(&s.repeat(0)), "");
    }

    #[test]
    fn test_repeat_one() {
        let s = st("hello");
        assert_eq!(to_std(&s.repeat(1)), "hello");
    }

    #[test]
    fn test_repeat_empty() {
        let s = st("");
        assert_eq!(to_std(&s.repeat(5)), "");
    }

    #[test]
    fn test_repeat_unicode() {
        let s = st("日本");
        assert_eq!(to_std(&s.repeat(2)), "日本日本");
    }
}

// =============================================================================
// Iterator edge case tests
// =============================================================================

mod iterator_edge_cases {
    use super::*;

    // Lines iterator edge cases
    #[test]
    fn test_lines_empty() {
        let s = st("");
        let lines: Vec<_> = s.lines().collect();
        assert!(lines.is_empty());
    }

    #[test]
    fn test_lines_single_no_newline() {
        let s = st("hello");
        let lines: Vec<_> = s.lines().map(|l| to_std(l)).collect();
        assert_eq!(lines, vec!["hello"]);
    }

    #[test]
    fn test_lines_crlf() {
        let s = st("hello\r\nworld\r\n");
        let lines: Vec<_> = s.lines().map(|l| to_std(l)).collect();
        assert_eq!(lines, vec!["hello", "world"]);
    }

    #[test]
    fn test_lines_mixed_endings() {
        let s = st("a\nb\r\nc\rd");
        let lines: Vec<_> = s.lines().map(|l| to_std(l)).collect();
        assert_eq!(lines, vec!["a", "b", "c\rd"]);
    }

    #[test]
    fn test_lines_empty_lines() {
        let s = st("a\n\nb");
        let lines: Vec<_> = s.lines().map(|l| to_std(l)).collect();
        assert_eq!(lines, vec!["a", "", "b"]);
    }

    // Split edge cases
    #[test]
    fn test_split_empty_string() {
        let s = st("");
        let parts: Vec<_> = s.split('-').map(|p| to_std(p)).collect();
        assert_eq!(parts, vec![""]);
    }

    #[test]
    fn test_split_no_match() {
        let s = st("hello");
        let parts: Vec<_> = s.split('-').map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["hello"]);
    }

    #[test]
    fn test_split_all_delimiters() {
        let s = st("---");
        let parts: Vec<_> = s.split('-').map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["", "", "", ""]);
    }

    #[test]
    fn test_splitn_zero() {
        let s = st("a-b-c");
        let parts: Vec<_> = s.splitn(0, '-').map(|p| to_std(p)).collect();
        assert!(parts.is_empty());
    }

    #[test]
    fn test_splitn_one() {
        let s = st("a-b-c");
        let parts: Vec<_> = s.splitn(1, '-').map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["a-b-c"]);
    }

    #[test]
    fn test_splitn_more_than_matches() {
        let s = st("a-b");
        let parts: Vec<_> = s.splitn(10, '-').map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["a", "b"]);
    }

    #[test]
    fn test_rsplitn_zero() {
        let s = st("a-b-c");
        let parts: Vec<_> = s.rsplitn(0, '-').map(|p| to_std(p)).collect();
        assert!(parts.is_empty());
    }

    #[test]
    fn test_rsplitn_one() {
        let s = st("a-b-c");
        let parts: Vec<_> = s.rsplitn(1, '-').map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["a-b-c"]);
    }

    #[test]
    fn test_rsplit_terminator() {
        let s = st("a-b-c-");
        let parts: Vec<_> = s.rsplit_terminator('-').map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["c", "b", "a"]);
    }

    #[test]
    fn test_rsplit_terminator_no_trailing() {
        let s = st("a-b-c");
        let parts: Vec<_> = s.rsplit_terminator('-').map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["c", "b", "a"]);
    }

    // Chars edge cases
    #[test]
    fn test_chars_empty() {
        let s = st("");
        assert_eq!(s.chars().count(), 0);
    }

    #[test]
    fn test_chars_single() {
        let s = st("a");
        let chars: Vec<_> = s.chars().collect();
        assert_eq!(chars, vec!['a']);
    }

    #[test]
    fn test_chars_rev_single() {
        let s = st("a");
        let chars: Vec<_> = s.chars().rev().collect();
        assert_eq!(chars, vec!['a']);
    }

    #[test]
    fn test_char_indices_empty() {
        let s = st("");
        assert_eq!(s.char_indices().count(), 0);
    }

    // Bytes edge cases
    #[test]
    fn test_bytes_empty() {
        let s = st("");
        assert_eq!(s.bytes().count(), 0);
    }

    #[test]
    fn test_bytes_rev_single() {
        let s = st("a");
        let bytes: Vec<_> = s.bytes().rev().collect();
        assert_eq!(bytes, vec![b'a']);
    }
}

// =============================================================================
// Error handling tests
// =============================================================================

mod error_handling {
    use super::*;
    use stringly::error::EncodingError;

    #[test]
    fn test_encoding_error_display() {
        let err = EncodingError::new(5, Some(2));
        let display = format!("{}", err);
        assert!(display.contains("5"));
    }

    #[test]
    fn test_encoding_error_valid_up_to() {
        let err = EncodingError::new(10, None);
        assert_eq!(err.valid_up_to(), 10);
    }

    #[test]
    fn test_encoding_error_error_len_some() {
        let err = EncodingError::new(5, Some(3));
        assert_eq!(err.error_len(), Some(3));
    }

    #[test]
    fn test_encoding_error_error_len_none() {
        let err = EncodingError::new(5, None);
        assert_eq!(err.error_len(), None);
    }

    #[test]
    fn test_from_bytes_error() {
        let invalid = b"hello\xFFworld".to_vec();
        let err = Utf8String::from_bytes(invalid).unwrap_err();

        // Check we can get the bytes back
        let bytes = err.as_bytes();
        assert_eq!(bytes, b"hello\xFFworld");
    }

    #[test]
    fn test_from_bytes_error_into_bytes() {
        let invalid = b"hello\xFFworld".to_vec();
        let err = Utf8String::from_bytes(invalid).unwrap_err();

        // Check we can get the bytes back by consuming
        let bytes = err.into_bytes();
        assert_eq!(bytes, b"hello\xFFworld");
    }

    #[test]
    fn test_from_bytes_error_encoding_error() {
        let invalid = b"hello\xFFworld".to_vec();
        let err = Utf8String::from_bytes(invalid).unwrap_err();

        let encoding_err = err.encoding_error();
        assert_eq!(encoding_err.valid_up_to(), 5); // Error at position 5
    }

    #[test]
    fn test_from_bytes_error_display() {
        let invalid = b"hello\xFFworld".to_vec();
        let err = Utf8String::from_bytes(invalid).unwrap_err();

        let display = format!("{}", err);
        assert!(!display.is_empty());
    }
}

// =============================================================================
// Phase 3: replace_range() grow/shrink tests
// =============================================================================

mod replace_range_paths {
    use super::*;

    #[test]
    fn test_replace_range_grow() {
        // Replacement larger than original
        let mut s = s("abc");
        s.replace_range(1..2, st("XXXXX")); // "b" -> "XXXXX"
        assert_eq!(to_std(&s), "aXXXXXc");
    }

    #[test]
    fn test_replace_range_shrink() {
        // Replacement smaller than original
        let mut s = s("abcdefgh");
        s.replace_range(2..6, st("X")); // "cdef" -> "X"
        assert_eq!(to_std(&s), "abXgh");
    }

    #[test]
    fn test_replace_range_equal_size() {
        let mut s = s("abcde");
        s.replace_range(1..4, st("XYZ")); // "bcd" -> "XYZ"
        assert_eq!(to_std(&s), "aXYZe");
    }

    #[test]
    fn test_replace_range_grow_unicode() {
        let mut s = s("日X語");
        s.replace_range(3..4, st("本本本")); // "X" -> "本本本"
        assert_eq!(to_std(&s), "日本本本語");
    }

    #[test]
    fn test_replace_range_shrink_unicode() {
        let mut s = s("日本本本語");
        s.replace_range(3..12, st("X")); // "本本本" -> "X"
        assert_eq!(to_std(&s), "日X語");
    }

    #[test]
    fn test_replace_range_from_start() {
        let mut s = s("hello world");
        s.replace_range(..5, st("goodbye"));
        assert_eq!(to_std(&s), "goodbye world");
    }

    #[test]
    fn test_replace_range_to_end() {
        let mut s = s("hello world");
        s.replace_range(6.., st("rust"));
        assert_eq!(to_std(&s), "hello rust");
    }

    #[test]
    fn test_replace_range_with_empty() {
        let mut s = s("hello world");
        s.replace_range(5..6, st("")); // Remove space
        assert_eq!(to_std(&s), "helloworld");
    }

    #[test]
    fn test_replace_range_empty_at_position() {
        let mut s = s("ab");
        s.replace_range(1..1, st("X")); // Insert without replacing
        assert_eq!(to_std(&s), "aXb");
    }
}

// =============================================================================
// Phase 3: Empty pattern tests
// =============================================================================

mod empty_pattern {
    use super::*;

    #[test]
    fn test_find_empty_pattern() {
        let s = st("hello");
        // Empty pattern should match at position 0
        assert_eq!(s.find(st("")), Some(0));
    }

    #[test]
    fn test_rfind_empty_pattern() {
        let s = st("hello");
        // Empty pattern should match at the end
        assert_eq!(s.rfind(st("")), Some(5));
    }

    #[test]
    fn test_contains_empty_pattern() {
        let s = st("hello");
        assert!(s.contains(st("")));

        let empty = st("");
        assert!(empty.contains(st("")));
    }

    #[test]
    fn test_split_empty_pattern() {
        let s = st("abc");
        // Splitting by empty pattern should yield each character
        let parts: Vec<_> = s.split(st("")).map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["", "a", "b", "c", ""]);
    }

    #[test]
    fn test_rsplit_empty_pattern() {
        let s = st("abc");
        let parts: Vec<_> = s.rsplit(st("")).map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["", "c", "b", "a", ""]);
    }

    #[test]
    fn test_split_empty_string_empty_pattern() {
        let s = st("");
        let parts: Vec<_> = s.split(st("")).map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["", ""]);
    }

    #[test]
    fn test_matches_empty_pattern() {
        let s = st("ab");
        let matches: Vec<_> = s.matches(st("")).map(|m| to_std(m)).collect();
        // Empty pattern matches at each position including boundaries
        assert_eq!(matches, vec!["", "", ""]);
    }

    #[test]
    fn test_match_indices_empty_pattern() {
        let s = st("ab");
        let indices: Vec<_> = s.match_indices(st("")).collect();
        assert_eq!(indices.len(), 3); // Positions 0, 1, 2
    }

    #[test]
    fn test_starts_with_empty() {
        let s = st("hello");
        assert!(s.starts_with(st("")));

        let empty = st("");
        assert!(empty.starts_with(st("")));
    }

    #[test]
    fn test_ends_with_empty() {
        let s = st("hello");
        assert!(s.ends_with(st("")));

        let empty = st("");
        assert!(empty.ends_with(st("")));
    }

    #[test]
    fn test_strip_prefix_empty() {
        let s = st("hello");
        let stripped = s.strip_prefix(st(""));
        assert_eq!(stripped.map(|s| to_std(s)), Some("hello".to_string()));
    }

    #[test]
    fn test_strip_suffix_empty() {
        let s = st("hello");
        let stripped = s.strip_suffix(st(""));
        assert_eq!(stripped.map(|s| to_std(s)), Some("hello".to_string()));
    }
}

// =============================================================================
// Phase 3: Drain double-ended tests
// =============================================================================

mod drain_advanced {
    use super::*;

    #[test]
    fn test_drain_rev() {
        let mut s = s("hello");
        let drained: std::string::String = s.drain(..).rev().collect();
        assert_eq!(drained, "olleh");
        assert_eq!(to_std(&s), "");
    }

    #[test]
    fn test_drain_partial_rev() {
        let mut s = s("hello world");
        let drained: std::string::String = s.drain(6..).rev().collect();
        assert_eq!(drained, "dlrow");
        assert_eq!(to_std(&s), "hello ");
    }

    #[test]
    fn test_drain_alternating() {
        let mut s = s("abcde");
        let mut drain = s.drain(..);
        assert_eq!(drain.next(), Some('a'));
        assert_eq!(drain.next_back(), Some('e'));
        assert_eq!(drain.next(), Some('b'));
        assert_eq!(drain.next_back(), Some('d'));
        assert_eq!(drain.next(), Some('c'));
        assert_eq!(drain.next(), None);
        assert_eq!(drain.next_back(), None);
        drop(drain);
        assert_eq!(to_std(&s), "");
    }

    #[test]
    fn test_drain_unicode_rev() {
        let mut s = s("日本語");
        let drained: std::string::String = s.drain(..).rev().collect();
        assert_eq!(drained, "語本日");
    }

    #[test]
    fn test_drain_empty_range() {
        let mut s = s("hello");
        let drained: std::string::String = s.drain(2..2).collect();
        assert_eq!(drained, "");
        assert_eq!(to_std(&s), "hello");
    }

    #[test]
    fn test_drain_size_hint() {
        let mut s = s("hello");
        let drain = s.drain(..);
        let (lower, upper) = drain.size_hint();
        // Should return exact char count
        assert_eq!(lower, 5);
        assert_eq!(upper, Some(5));
    }

    #[test]
    fn test_drain_size_hint_unicode() {
        let mut s = s("日本語"); // 3 chars, 9 bytes
        let drain = s.drain(..);
        let (lower, upper) = drain.size_hint();
        assert_eq!(lower, 3);
        assert_eq!(upper, Some(3));
    }
}

// =============================================================================
// Phase 3: insert() unicode edge cases
// =============================================================================

mod insert_unicode {
    use super::*;

    #[test]
    fn test_insert_at_end() {
        let mut s = s("hello");
        s.insert(5, '!');
        assert_eq!(to_std(&s), "hello!");
    }

    #[test]
    fn test_insert_into_empty() {
        let mut s = s("");
        s.insert(0, 'X');
        assert_eq!(to_std(&s), "X");
    }

    #[test]
    fn test_insert_3byte_char() {
        let mut s = s("ab");
        s.insert(1, '中'); // 3-byte UTF-8
        assert_eq!(to_std(&s), "a中b");
    }

    #[test]
    fn test_insert_4byte_char() {
        let mut s = s("ab");
        s.insert(1, '𤭢'); // 4-byte UTF-8
        assert_eq!(to_std(&s), "a𤭢b");
    }

    #[test]
    fn test_insert_str_at_end() {
        let mut s = s("hello");
        s.insert_str(5, st(" world"));
        assert_eq!(to_std(&s), "hello world");
    }

    #[test]
    fn test_insert_str_into_empty() {
        let mut s = s("");
        s.insert_str(0, st("hello"));
        assert_eq!(to_std(&s), "hello");
    }

    #[test]
    fn test_insert_empty_str() {
        let mut s = s("hello");
        s.insert_str(2, st(""));
        assert_eq!(to_std(&s), "hello");
    }

    #[test]
    fn test_insert_str_unicode_at_unicode() {
        let mut s = s("日語");
        s.insert_str(3, st("本")); // After 日
        assert_eq!(to_std(&s), "日本語");
    }
}

// =============================================================================
// Phase 3: trim edge cases
// =============================================================================

mod trim_advanced {
    use super::*;

    #[test]
    fn test_trim_start_matches_closure() {
        let s = st("xxxyyyzzz");
        let trimmed = s.trim_start_matches(|c: char| c == 'x');
        assert_eq!(to_std(trimmed), "yyyzzz");
    }

    #[test]
    fn test_trim_end_matches_closure() {
        let s = st("xxxyyyzzz");
        let trimmed = s.trim_end_matches(|c: char| c == 'z');
        assert_eq!(to_std(trimmed), "xxxyyy");
    }

    #[test]
    fn test_trim_matches_closure() {
        let s = st("xxxyyyxxx");
        let trimmed = s.trim_matches(|c: char| c == 'x');
        assert_eq!(to_std(trimmed), "yyy");
    }

    #[test]
    fn test_trim_start_matches_all() {
        let s = st("xxxxx");
        let trimmed = s.trim_start_matches('x');
        assert_eq!(to_std(trimmed), "");
    }

    #[test]
    fn test_trim_end_matches_all() {
        let s = st("xxxxx");
        let trimmed = s.trim_end_matches('x');
        assert_eq!(to_std(trimmed), "");
    }

    #[test]
    fn test_trim_start_matches_none() {
        let s = st("hello");
        let trimmed = s.trim_start_matches('x');
        assert_eq!(to_std(trimmed), "hello");
    }

    #[test]
    fn test_trim_end_matches_none() {
        let s = st("hello");
        let trimmed = s.trim_end_matches('x');
        assert_eq!(to_std(trimmed), "hello");
    }

    #[test]
    fn test_trim_unicode_whitespace() {
        // U+3000 is ideographic space
        let s = st("\u{3000}hello\u{3000}");
        assert_eq!(to_std(s.trim()), "hello");
    }

    #[test]
    fn test_trim_start_matches_str() {
        let s = st("hahaha world");
        let trimmed = s.trim_start_matches(st("ha"));
        assert_eq!(to_std(trimmed), " world");
    }

    #[test]
    fn test_trim_end_matches_str() {
        let s = st("world hahaha");
        let trimmed = s.trim_end_matches(st("ha"));
        assert_eq!(to_std(trimmed), "world ");
    }
}

// =============================================================================
// Phase 3: CharSlice searcher tests
// =============================================================================

mod char_slice_pattern {
    use super::*;

    #[test]
    fn test_find_char_slice() {
        let s = st("hello world");
        let chars: &[char] = &['o', 'w'];
        assert_eq!(s.find(chars), Some(4)); // First 'o'
    }

    #[test]
    fn test_find_char_slice_single() {
        let s = st("hello");
        let chars: &[char] = &['e'];
        assert_eq!(s.find(chars), Some(1));
    }

    #[test]
    fn test_rfind_char_slice() {
        let s = st("hello world");
        let chars: &[char] = &['o', 'l'];
        assert_eq!(s.rfind(chars), Some(9)); // Last 'l'
    }

    #[test]
    fn test_contains_char_slice() {
        let s = st("hello");
        let chars: &[char] = &['x', 'y', 'e'];
        assert!(s.contains(chars)); // Contains 'e'
    }

    #[test]
    fn test_not_contains_char_slice() {
        let s = st("hello");
        let chars: &[char] = &['x', 'y', 'z'];
        assert!(!s.contains(chars));
    }

    #[test]
    fn test_split_char_slice() {
        let s = st("a,b;c");
        let chars: &[char] = &[',', ';'];
        let parts: Vec<_> = s.split(chars).map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["a", "b", "c"]);
    }

    #[test]
    fn test_trim_matches_char_slice() {
        let s = st("...hello...");
        let chars: &[char] = &['.'];
        assert_eq!(to_std(s.trim_matches(chars)), "hello");
    }

    #[test]
    fn test_matches_char_slice() {
        let s = st("abcabc");
        let chars: &[char] = &['a', 'c'];
        let matches: Vec<_> = s.matches(chars).map(|m| to_std(m)).collect();
        assert_eq!(matches, vec!["a", "c", "a", "c"]);
    }

    #[test]
    fn test_char_slice_unicode() {
        let s = st("日本語テスト");
        let chars: &[char] = &['本', 'ス'];
        assert_eq!(s.find(chars), Some(3)); // '本' at byte 3
    }
}

// =============================================================================
// Phase 3: extend_from_within() tests
// =============================================================================

mod extend_from_within {
    use super::*;

    #[test]
    fn test_extend_from_within_full() {
        let mut s = s("abc");
        s.extend_from_within(..);
        assert_eq!(to_std(&s), "abcabc");
    }

    #[test]
    fn test_extend_from_within_start() {
        let mut s = s("hello world");
        s.extend_from_within(..5);
        assert_eq!(to_std(&s), "hello worldhello");
    }

    #[test]
    fn test_extend_from_within_end() {
        let mut s = s("hello world");
        s.extend_from_within(6..);
        assert_eq!(to_std(&s), "hello worldworld");
    }

    #[test]
    fn test_extend_from_within_middle() {
        let mut s = s("hello world");
        s.extend_from_within(3..8);
        assert_eq!(to_std(&s), "hello worldlo wo");
    }

    #[test]
    fn test_extend_from_within_empty() {
        let mut s = s("hello");
        s.extend_from_within(2..2);
        assert_eq!(to_std(&s), "hello");
    }

    #[test]
    fn test_extend_from_within_unicode() {
        let mut s = s("日本語");
        s.extend_from_within(3..6); // Just '本'
        assert_eq!(to_std(&s), "日本語本");
    }

    #[test]
    fn test_extend_from_within_inclusive() {
        let mut s = s("abc");
        s.extend_from_within(0..=1);
        assert_eq!(to_std(&s), "abcab");
    }
}

// =============================================================================
// Phase 3: TranscodeError tests
// =============================================================================

mod transcode_tests {
    use super::*;
    use stringly::{Utf16Be, Utf16Le, Utf32Le};

    #[test]
    fn test_transcode_utf8_to_utf16le() {
        let utf8_str = st("hello世界");
        let result: Result<stringly::String<Utf16Le>, _> = utf8_str.try_transcode();
        assert!(result.is_ok());
        let utf16 = result.unwrap();
        assert_eq!(utf16.chars().count(), 7);
    }

    #[test]
    fn test_transcode_utf8_to_utf16be() {
        let utf8_str = st("hello");
        let result: Result<stringly::String<Utf16Be>, _> = utf8_str.try_transcode();
        assert!(result.is_ok());
    }

    #[test]
    fn test_transcode_utf8_to_utf32() {
        let utf8_str = st("hello世界");
        let result: Result<stringly::String<Utf32Le>, _> = utf8_str.try_transcode();
        assert!(result.is_ok());
        let utf32 = result.unwrap();
        assert_eq!(utf32.chars().count(), 7);
    }

    #[test]
    fn test_transcode_roundtrip() {
        let utf8_str = st("hello世界🎉");
        let utf16: stringly::String<Utf16Le> = utf8_str.try_transcode().unwrap();
        let back: Utf8String = utf16.as_str().try_transcode().unwrap();
        assert_eq!(to_std(&back), "hello世界🎉");
    }

    #[test]
    fn test_transcode_empty() {
        let utf8_str = st("");
        let result: Result<stringly::String<Utf16Le>, _> = utf8_str.try_transcode();
        assert!(result.is_ok());
        assert_eq!(result.unwrap().len(), 0);
    }
}

// =============================================================================
// Phase 3: Index operations advanced
// =============================================================================

mod index_advanced {
    use super::*;

    #[test]
    fn test_index_range_inclusive() {
        let s = s("hello");
        let slice: &Utf8Str = &s[0..=2];
        assert_eq!(to_std(slice), "hel");
    }

    #[test]
    fn test_index_range_inclusive_unicode() {
        let s = s("日本語");
        let slice: &Utf8Str = &s[0..=5]; // 日本
        assert_eq!(to_std(slice), "日本");
    }

    #[test]
    #[should_panic]
    fn test_index_range_out_of_bounds() {
        let s = s("hello");
        let _: &Utf8Str = &s[0..10];
    }

    #[test]
    #[should_panic]
    fn test_index_range_bad_boundary() {
        let s = s("日本語");
        let _: &Utf8Str = &s[0..1]; // Not a char boundary
    }

    #[test]
    #[should_panic]
    fn test_index_range_from_out_of_bounds() {
        let s = s("hello");
        let _: &Utf8Str = &s[10..];
    }

    #[test]
    #[should_panic]
    fn test_index_range_to_bad_boundary() {
        let s = s("日本語");
        let _: &Utf8Str = &s[..1]; // Not a char boundary
    }

    #[test]
    fn test_get_valid() {
        let s = st("hello");
        assert_eq!(s.get(0..3).map(|s| to_std(s)), Some("hel".to_string()));
    }

    #[test]
    fn test_get_out_of_bounds() {
        let s = st("hello");
        assert!(s.get(0..10).is_none());
    }
}

// =============================================================================
// Phase 3: Iterator advanced tests
// =============================================================================

mod iterator_advanced {
    use super::*;

    #[test]
    fn test_char_indices_bidirectional() {
        let s = st("abc");
        let mut iter = s.char_indices();
        assert_eq!(iter.next(), Some((0, 'a')));
        assert_eq!(iter.next_back(), Some((2, 'c')));
        assert_eq!(iter.next(), Some((1, 'b')));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn test_bytes_size_hint() {
        let s = st("hello");
        let bytes = s.bytes();
        assert_eq!(bytes.size_hint(), (5, Some(5)));
    }

    #[test]
    fn test_chars_size_hint_ascii() {
        let s = st("hello");
        let chars = s.chars();
        let (lower, upper) = chars.size_hint();
        assert!(lower <= 5);
        assert!(upper.unwrap() >= 5);
    }

    #[test]
    fn test_split_inclusive_last_no_match() {
        let s = st("abc");
        let parts: Vec<_> = s.split_inclusive('-').map(|p| to_std(p)).collect();
        // No delimiter found, entire string is one part
        assert_eq!(parts, vec!["abc"]);
    }

    #[test]
    fn test_split_terminator_empty_parts() {
        let s = st("--");
        let parts: Vec<_> = s.split_terminator('-').map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["", ""]);
    }

    #[test]
    fn test_split_inclusive_unicode() {
        let s = st("日-本-語");
        let parts: Vec<_> = s.split_inclusive('-').map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["日-", "本-", "語"]);
    }

    #[test]
    fn test_splitn_exact_count() {
        let s = st("a-b-c-d");
        let parts: Vec<_> = s.splitn(3, '-').map(|p| to_std(p)).collect();
        assert_eq!(parts, vec!["a", "b", "c-d"]);
    }
}
