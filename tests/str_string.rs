//! Comprehensive tests for Str<E> and String<E> types.
//!
//! These tests are based on the Rust standard library test suite:
//! - library/alloctests/tests/string.rs
//! - library/alloctests/tests/str.rs

use stringly::{Encoding, Str, String, Utf8, Utf16Be, Utf16Le};
#[cfg(feature = "utf32")]
use stringly::{Utf32Be, Utf32Le};

// Helper to create a string for any encoding
fn make_string<E: Encoding>(s: &str) -> String<E> {
    s.chars().collect()
}

// Helper to compare string content
fn str_eq<E: Encoding>(s: &Str<E>, expected: &str) -> bool {
    s.chars().eq(expected.chars())
}

// =============================================================================
// Macro to generate tests for all encodings
// =============================================================================

macro_rules! test_for_all_encodings {
    ($test_name:ident) => {
        paste::paste! {
            #[test]
            fn [<$test_name _utf8>]() {
                $test_name::<Utf8>();
            }

            #[test]
            fn [<$test_name _utf16le>]() {
                $test_name::<Utf16Le>();
            }

            #[test]
            fn [<$test_name _utf16be>]() {
                $test_name::<Utf16Be>();
            }

            #[cfg(feature = "utf32")]
            #[test]
            fn [<$test_name _utf32le>]() {
                $test_name::<Utf32Le>();
            }

            #[cfg(feature = "utf32")]
            #[test]
            fn [<$test_name _utf32be>]() {
                $test_name::<Utf32Be>();
            }
        }
    };
}

// =============================================================================
// String<E> Construction Tests
// =============================================================================

fn test_from_char<E: Encoding>() {
    let s: String<E> = String::from('a');
    assert!(str_eq(&s, "a"));

    let s: String<E> = String::from('é');
    assert!(str_eq(&s, "é"));

    // Emoji (surrogate pair in UTF-16)
    let s: String<E> = String::from('😀');
    assert!(str_eq(&s, "😀"));
}

test_for_all_encodings!(test_from_char);

fn test_collect<E: Encoding>() {
    let s: String<E> = "hello".chars().collect();
    assert!(str_eq(&s, "hello"));

    let s: String<E> = "héllo 世界".chars().collect();
    assert!(str_eq(&s, "héllo 世界"));

    let s: String<E> = "".chars().collect();
    assert!(s.is_empty());
}

test_for_all_encodings!(test_collect);

fn test_new_empty<E: Encoding>() {
    let s: String<E> = String::new();
    assert!(s.is_empty());
    assert_eq!(s.len(), 0);
}

test_for_all_encodings!(test_new_empty);

fn test_with_capacity<E: Encoding>() {
    let s: String<E> = String::with_capacity(100);
    assert!(s.is_empty());
    assert!(s.capacity() >= 100);
}

test_for_all_encodings!(test_with_capacity);

// =============================================================================
// String<E> Mutation Tests
// =============================================================================

fn test_push<E: Encoding>() {
    let mut s: String<E> = String::new();
    s.push('a');
    assert!(str_eq(&s, "a"));

    s.push('b');
    assert!(str_eq(&s, "ab"));

    s.push('é');
    assert!(str_eq(&s, "abé"));

    s.push('😀');
    assert!(str_eq(&s, "abé😀"));
}

test_for_all_encodings!(test_push);

fn test_push_str<E: Encoding>() {
    let mut s: String<E> = String::new();
    let hello: String<E> = make_string("hello");
    s.push_str(&hello);
    assert!(str_eq(&s, "hello"));

    let world: String<E> = make_string(" world");
    s.push_str(&world);
    assert!(str_eq(&s, "hello world"));
}

test_for_all_encodings!(test_push_str);

fn test_pop<E: Encoding>() {
    let mut s: String<E> = make_string("hello");

    assert_eq!(s.pop(), Some('o'));
    assert!(str_eq(&s, "hell"));

    assert_eq!(s.pop(), Some('l'));
    assert_eq!(s.pop(), Some('l'));
    assert_eq!(s.pop(), Some('e'));
    assert_eq!(s.pop(), Some('h'));
    assert_eq!(s.pop(), None);
    assert!(s.is_empty());
}

test_for_all_encodings!(test_pop);

fn test_pop_unicode<E: Encoding>() {
    let mut s: String<E> = make_string("héllo😀");

    assert_eq!(s.pop(), Some('😀'));
    assert_eq!(s.pop(), Some('o'));
    assert_eq!(s.pop(), Some('l'));
    assert_eq!(s.pop(), Some('l'));
    assert_eq!(s.pop(), Some('é'));
    assert_eq!(s.pop(), Some('h'));
    assert_eq!(s.pop(), None);
}

test_for_all_encodings!(test_pop_unicode);

fn test_clear<E: Encoding>() {
    let mut s: String<E> = make_string("hello");
    s.clear();
    assert!(s.is_empty());
    assert_eq!(s.len(), 0);
}

test_for_all_encodings!(test_clear);

fn test_truncate<E: Encoding>() {
    let mut s: String<E> = make_string("hello");

    // Find the byte position of the third char boundary (after "he")
    let mut char_boundaries: Vec<usize> = vec![0];
    for (i, _) in s.char_indices() {
        if i > 0 {
            char_boundaries.push(i);
        }
    }
    char_boundaries.push(s.len());

    // Truncate to keep first 2 chars
    let truncate_pos = char_boundaries[2]; // Position after 2nd char
    s.truncate(truncate_pos);
    assert!(str_eq(&s, "he"));

    s.truncate(0);
    assert!(s.is_empty());
}

test_for_all_encodings!(test_truncate);

#[test]
#[should_panic]
fn test_truncate_invalid_utf8() {
    let mut s: String<Utf8> = make_string("héllo");
    // 'é' is 2 bytes in UTF-8, truncating at byte 2 would split it
    s.truncate(2);
}

fn test_insert<E: Encoding>() {
    let mut s: String<E> = make_string("hello");

    // Insert at beginning
    s.insert(0, 'X');
    assert!(str_eq(&s, "Xhello"));

    // Insert at end
    let len = s.len();
    s.insert(len, 'Y');
    assert!(str_eq(&s, "XhelloY"));
}

test_for_all_encodings!(test_insert);

fn test_remove<E: Encoding>() {
    let mut s: String<E> = make_string("hello");

    let c = s.remove(0);
    assert_eq!(c, 'h');
    assert!(str_eq(&s, "ello"));

    let c = s.remove(0);
    assert_eq!(c, 'e');
    assert!(str_eq(&s, "llo"));
}

test_for_all_encodings!(test_remove);

fn test_retain<E: Encoding>() {
    let mut s: String<E> = make_string("hello");
    s.retain(|c| c != 'l');
    assert!(str_eq(&s, "heo"));
}

test_for_all_encodings!(test_retain);

// =============================================================================
// String<E> Drain Tests
// =============================================================================

fn test_drain<E: Encoding>() {
    let mut s: String<E> = make_string("hello");

    // Get char boundaries
    let boundaries: Vec<usize> = s.char_indices().map(|(i, _)| i).collect();
    // boundaries = positions of h, e, l, l, o

    // Drain "ell" (chars 1..4)
    let start = boundaries[1]; // 'e'
    let end = boundaries[4]; // 'o' (exclusive)

    let drained: std::string::String = s.drain(start..end).collect();
    assert_eq!(drained, "ell");
    assert!(str_eq(&s, "ho"));
}

test_for_all_encodings!(test_drain);

fn test_drain_full<E: Encoding>() {
    let mut s: String<E> = make_string("hello");
    let drained: std::string::String = s.drain(..).collect();
    assert_eq!(drained, "hello");
    assert!(s.is_empty());
}

test_for_all_encodings!(test_drain_full);

// =============================================================================
// String<E> Replace Range Tests
// =============================================================================

fn test_replace_range<E: Encoding>() {
    let mut s: String<E> = make_string("hello");

    // Get char boundaries
    let boundaries: Vec<usize> = s.char_indices().map(|(i, _)| i).collect();

    // Replace "ell" (chars 1..4) with "XYZ"
    let start = boundaries[1];
    let end = boundaries[4];

    let replacement: String<E> = make_string("XYZ");
    s.replace_range(start..end, &replacement);
    assert!(str_eq(&s, "hXYZo"));
}

test_for_all_encodings!(test_replace_range);

fn test_replace_range_empty<E: Encoding>() {
    let mut s: String<E> = make_string("hello");

    // Get char boundaries
    let boundaries: Vec<usize> = s.char_indices().map(|(i, _)| i).collect();

    // Replace "ell" (chars 1..4) with empty
    let start = boundaries[1];
    let end = boundaries[4];

    let empty: String<E> = make_string("");
    s.replace_range(start..end, &empty);
    assert!(str_eq(&s, "ho"));
}

test_for_all_encodings!(test_replace_range_empty);

// =============================================================================
// Str<E> Finding Tests
// =============================================================================

fn test_find<E: Encoding>() {
    let s: String<E> = make_string("hello world");

    // Find returns byte position, which varies by encoding
    // Check that find returns Some and the char at that position is correct
    let w_pos = s.find('w');
    assert!(w_pos.is_some());
    // Verify we can use the position
    let w_idx = w_pos.unwrap();
    assert!(s.is_char_boundary(w_idx));

    assert_eq!(s.find('h'), Some(0)); // First char is always at 0
    assert!(s.find('d').is_some());
    assert_eq!(s.find('x'), None);
}

test_for_all_encodings!(test_find);

fn test_rfind<E: Encoding>() {
    let s: String<E> = make_string("hello world");

    // rfind returns byte position, which varies by encoding
    let o_pos = s.rfind('o');
    assert!(o_pos.is_some());
    assert!(s.is_char_boundary(o_pos.unwrap()));

    let l_pos = s.rfind('l');
    assert!(l_pos.is_some());
    assert!(s.is_char_boundary(l_pos.unwrap()));

    assert_eq!(s.rfind('x'), None);
}

test_for_all_encodings!(test_rfind);

fn test_contains<E: Encoding>() {
    let s: String<E> = make_string("hello");

    assert!(s.contains('h'));
    assert!(s.contains('e'));
    assert!(s.contains('o'));
    assert!(!s.contains('x'));
}

test_for_all_encodings!(test_contains);

fn test_starts_with<E: Encoding>() {
    let s: String<E> = make_string("hello");

    assert!(s.starts_with('h'));
    assert!(!s.starts_with('e'));
    assert!(!s.starts_with('x'));
}

test_for_all_encodings!(test_starts_with);

fn test_ends_with<E: Encoding>() {
    let s: String<E> = make_string("hello");

    assert!(s.ends_with('o'));
    assert!(!s.ends_with('l'));
    assert!(!s.ends_with('x'));
}

test_for_all_encodings!(test_ends_with);

// =============================================================================
// Str<E> Splitting Tests
// =============================================================================

fn test_split<E: Encoding>() {
    let s: String<E> = make_string("a,b,c");
    let parts: Vec<std::string::String> = s.split(',').map(|p| p.chars().collect()).collect();
    assert_eq!(parts, vec!["a", "b", "c"]);
}

test_for_all_encodings!(test_split);

fn test_split_whitespace<E: Encoding>() {
    let s: String<E> = make_string("  hello   world  ");
    let parts: Vec<std::string::String> =
        s.split_whitespace().map(|p| p.chars().collect()).collect();
    assert_eq!(parts, vec!["hello", "world"]);
}

test_for_all_encodings!(test_split_whitespace);

fn test_split_once<E: Encoding>() {
    let s: String<E> = make_string("a:b:c");

    if let Some((before, after)) = s.split_once(':') {
        assert!(str_eq(before, "a"));
        assert!(str_eq(after, "b:c"));
    } else {
        panic!("split_once should have found ':'");
    }
}

test_for_all_encodings!(test_split_once);

fn test_rsplit_once<E: Encoding>() {
    let s: String<E> = make_string("a:b:c");

    if let Some((before, after)) = s.rsplit_once(':') {
        assert!(str_eq(before, "a:b"));
        assert!(str_eq(after, "c"));
    } else {
        panic!("rsplit_once should have found ':'");
    }
}

test_for_all_encodings!(test_rsplit_once);

fn test_lines<E: Encoding>() {
    let s: String<E> = make_string("hello\nworld\n");
    let lines: Vec<std::string::String> = s.lines().map(|l| l.chars().collect()).collect();
    assert_eq!(lines, vec!["hello", "world"]);
}

test_for_all_encodings!(test_lines);

fn test_lines_crlf<E: Encoding>() {
    let s: String<E> = make_string("hello\r\nworld\r\n");
    let lines: Vec<std::string::String> = s.lines().map(|l| l.chars().collect()).collect();
    assert_eq!(lines, vec!["hello", "world"]);
}

test_for_all_encodings!(test_lines_crlf);

// =============================================================================
// Str<E> Iteration Tests
// =============================================================================

fn test_chars<E: Encoding>() {
    let s: String<E> = make_string("héllo");
    let chars: Vec<char> = s.chars().collect();
    assert_eq!(chars, vec!['h', 'é', 'l', 'l', 'o']);
}

test_for_all_encodings!(test_chars);

fn test_chars_rev<E: Encoding>() {
    let s: String<E> = make_string("hello");
    let chars: Vec<char> = s.chars().rev().collect();
    assert_eq!(chars, vec!['o', 'l', 'l', 'e', 'h']);
}

test_for_all_encodings!(test_chars_rev);

fn test_chars_emoji<E: Encoding>() {
    let s: String<E> = make_string("a😀b");
    let chars: Vec<char> = s.chars().collect();
    assert_eq!(chars, vec!['a', '😀', 'b']);
}

test_for_all_encodings!(test_chars_emoji);

fn test_char_indices<E: Encoding>() {
    let s: String<E> = make_string("hello");
    let indices: Vec<(usize, char)> = s.char_indices().collect();

    // Check chars are correct
    let chars: Vec<char> = indices.iter().map(|(_, c)| *c).collect();
    assert_eq!(chars, vec!['h', 'e', 'l', 'l', 'o']);

    // Check indices are ascending
    let mut prev = 0;
    for (i, (idx, _)) in indices.iter().enumerate() {
        if i > 0 {
            assert!(*idx > prev);
        }
        prev = *idx;
    }
}

test_for_all_encodings!(test_char_indices);

fn test_bytes<E: Encoding>() {
    let s: String<E> = make_string("hello");
    let byte_count = s.bytes().count();
    assert!(byte_count >= 5); // At least 5 bytes for "hello"
}

test_for_all_encodings!(test_bytes);

fn test_iterator_last<E: Encoding>() {
    let s: String<E> = make_string("hello");
    assert_eq!(s.chars().last(), Some('o'));

    let empty: String<E> = make_string("");
    assert_eq!(empty.chars().last(), None);
}

test_for_all_encodings!(test_iterator_last);

fn test_iterator_nth<E: Encoding>() {
    let s: String<E> = make_string("hello");
    let mut chars = s.chars();

    assert_eq!(chars.nth(0), Some('h'));
    assert_eq!(chars.nth(1), Some('l')); // Skips 'e', returns 'l'
    assert_eq!(chars.nth(0), Some('l')); // Next char
    assert_eq!(chars.nth(0), Some('o'));
    assert_eq!(chars.nth(0), None);
}

test_for_all_encodings!(test_iterator_nth);

// =============================================================================
// Str<E> Trimming Tests
// =============================================================================

fn test_trim<E: Encoding>() {
    let s: String<E> = make_string("  hello  ");
    let trimmed = s.trim();
    assert!(str_eq(trimmed, "hello"));
}

test_for_all_encodings!(test_trim);

fn test_trim_start<E: Encoding>() {
    let s: String<E> = make_string("  hello  ");
    let trimmed = s.trim_start();
    assert!(str_eq(trimmed, "hello  "));
}

test_for_all_encodings!(test_trim_start);

fn test_trim_end<E: Encoding>() {
    let s: String<E> = make_string("  hello  ");
    let trimmed = s.trim_end();
    assert!(str_eq(trimmed, "  hello"));
}

test_for_all_encodings!(test_trim_end);

fn test_trim_matches<E: Encoding>() {
    let s: String<E> = make_string("xxhelloxx");
    let trimmed = s.trim_matches('x');
    assert!(str_eq(trimmed, "hello"));
}

test_for_all_encodings!(test_trim_matches);

fn test_trim_start_matches<E: Encoding>() {
    let s: String<E> = make_string("xxhelloxx");
    let trimmed = s.trim_start_matches('x');
    assert!(str_eq(trimmed, "helloxx"));
}

test_for_all_encodings!(test_trim_start_matches);

fn test_trim_end_matches<E: Encoding>() {
    let s: String<E> = make_string("xxhelloxx");
    let trimmed = s.trim_end_matches('x');
    assert!(str_eq(trimmed, "xxhello"));
}

test_for_all_encodings!(test_trim_end_matches);

fn test_strip_prefix<E: Encoding>() {
    let s: String<E> = make_string("hello");

    let stripped = s.strip_prefix('h');
    assert!(stripped.is_some());
    assert!(str_eq(stripped.unwrap(), "ello"));

    let not_stripped = s.strip_prefix('x');
    assert!(not_stripped.is_none());
}

test_for_all_encodings!(test_strip_prefix);

fn test_strip_suffix<E: Encoding>() {
    let s: String<E> = make_string("hello");

    let stripped = s.strip_suffix('o');
    assert!(stripped.is_some());
    assert!(str_eq(stripped.unwrap(), "hell"));

    let not_stripped = s.strip_suffix('x');
    assert!(not_stripped.is_none());
}

test_for_all_encodings!(test_strip_suffix);

// =============================================================================
// Str<E> Slicing and Boundary Tests
// =============================================================================

fn test_split_at<E: Encoding>() {
    let s: String<E> = make_string("hello");
    let len = s.len();

    // Split in middle (for UTF-8, this is at byte 2)
    // We need to find a valid char boundary
    let mut split_point = 0;
    for (i, _) in s.char_indices() {
        if i > 0 {
            split_point = i;
            break;
        }
    }

    let (left, right) = s.split_at(split_point);
    assert!(str_eq(left, "h"));
    assert!(str_eq(right, "ello"));

    // Split at start
    let (left, right) = s.split_at(0);
    assert!(left.is_empty());
    assert!(str_eq(right, "hello"));

    // Split at end
    let (left, right) = s.split_at(len);
    assert!(str_eq(left, "hello"));
    assert!(right.is_empty());
}

test_for_all_encodings!(test_split_at);

fn test_is_char_boundary<E: Encoding>() {
    let s: String<E> = make_string("hello");

    // Start and end are always boundaries
    assert!(s.is_char_boundary(0));
    assert!(s.is_char_boundary(s.len()));

    // Out of bounds
    assert!(!s.is_char_boundary(s.len() + 1));
}

test_for_all_encodings!(test_is_char_boundary);

fn test_get<E: Encoding>() {
    let s: String<E> = make_string("hello");

    // Find first char boundary after start
    let mut second_char_start = 0;
    for (i, _) in s.char_indices().skip(1) {
        second_char_start = i;
        break;
    }

    // Valid range
    let slice = s.get(0..second_char_start);
    assert!(slice.is_some());

    // Out of bounds
    let slice = s.get(0..s.len() + 1);
    assert!(slice.is_none());
}

test_for_all_encodings!(test_get);

fn test_is_empty<E: Encoding>() {
    let empty: String<E> = String::new();
    assert!(empty.is_empty());

    let not_empty: String<E> = make_string("a");
    assert!(!not_empty.is_empty());
}

test_for_all_encodings!(test_is_empty);

fn test_len<E: Encoding>() {
    let empty: String<E> = String::new();
    assert_eq!(empty.len(), 0);

    let s: String<E> = make_string("hello");
    assert!(s.len() > 0);
}

test_for_all_encodings!(test_len);

// =============================================================================
// Str<E> Case Conversion Tests
// =============================================================================

fn test_to_lowercase<E: Encoding>() {
    let s: String<E> = make_string("HELLO");
    let lower = s.to_lowercase();
    assert!(str_eq(&lower, "hello"));
}

test_for_all_encodings!(test_to_lowercase);

fn test_to_uppercase<E: Encoding>() {
    let s: String<E> = make_string("hello");
    let upper = s.to_uppercase();
    assert!(str_eq(&upper, "HELLO"));
}

test_for_all_encodings!(test_to_uppercase);

fn test_to_ascii_lowercase<E: Encoding>() {
    let s: String<E> = make_string("HELLO");
    let lower = s.to_ascii_lowercase();
    assert!(str_eq(&lower, "hello"));
}

test_for_all_encodings!(test_to_ascii_lowercase);

fn test_to_ascii_uppercase<E: Encoding>() {
    let s: String<E> = make_string("hello");
    let upper = s.to_ascii_uppercase();
    assert!(str_eq(&upper, "HELLO"));
}

test_for_all_encodings!(test_to_ascii_uppercase);

// =============================================================================
// Str<E> Replacement Tests
// =============================================================================

fn test_replace<E: Encoding>() {
    let s: String<E> = make_string("hello");
    let to: String<E> = make_string("X");
    let result = s.replace('l', &to);
    assert!(str_eq(&result, "heXXo"));
}

test_for_all_encodings!(test_replace);

fn test_replacen<E: Encoding>() {
    let s: String<E> = make_string("hello");
    let to: String<E> = make_string("X");
    let result = s.replacen('l', &to, 1);
    assert!(str_eq(&result, "heXlo"));
}

test_for_all_encodings!(test_replacen);

// =============================================================================
// Str<E> Misc Tests
// =============================================================================

fn test_repeat<E: Encoding>() {
    let s: String<E> = make_string("ab");
    let repeated = s.repeat(3);
    assert!(str_eq(&repeated, "ababab"));

    let repeated_zero = s.repeat(0);
    assert!(repeated_zero.is_empty());
}

test_for_all_encodings!(test_repeat);

fn test_is_ascii<E: Encoding>() {
    let ascii: String<E> = make_string("hello");
    assert!(ascii.is_ascii());

    let non_ascii: String<E> = make_string("héllo");
    assert!(!non_ascii.is_ascii());
}

test_for_all_encodings!(test_is_ascii);

fn test_eq_ignore_ascii_case<E: Encoding>() {
    let s1: String<E> = make_string("hello");
    let s2: String<E> = make_string("HELLO");
    assert!(s1.eq_ignore_ascii_case(&s2));

    let s3: String<E> = make_string("world");
    assert!(!s1.eq_ignore_ascii_case(&s3));
}

test_for_all_encodings!(test_eq_ignore_ascii_case);

fn test_parse<E: Encoding>() {
    let s: String<E> = make_string("42");
    let n: i32 = s.parse().unwrap();
    assert_eq!(n, 42);
}

test_for_all_encodings!(test_parse);

// =============================================================================
// Multi-Encoding Round-Trip Tests
// =============================================================================

fn test_roundtrip_ascii<E: Encoding>() {
    for c in 0u8..128 {
        let ch = c as char;
        let s: String<E> = String::from(ch);
        assert_eq!(s.chars().next(), Some(ch), "failed for ASCII {}", c);
    }
}

test_for_all_encodings!(test_roundtrip_ascii);

fn test_roundtrip_bmp<E: Encoding>() {
    // Test a selection of BMP characters
    let test_chars = [
        '\u{0080}', // First non-ASCII
        '\u{00FF}', // Latin-1 max
        '\u{0100}', // Latin Extended-A
        '\u{0400}', // Cyrillic
        '\u{4E00}', // CJK
        '\u{AC00}', // Hangul
        '\u{FFFD}', // Replacement char
    ];

    for &ch in &test_chars {
        let s: String<E> = String::from(ch);
        assert_eq!(s.chars().next(), Some(ch), "failed for U+{:04X}", ch as u32);
    }
}

test_for_all_encodings!(test_roundtrip_bmp);

fn test_roundtrip_supplementary<E: Encoding>() {
    // Test supplementary plane characters (require surrogate pairs in UTF-16)
    let test_chars = [
        '\u{10000}',  // First supplementary
        '\u{1F600}',  // 😀
        '\u{1F44D}',  // 👍
        '\u{10FFFF}', // Max Unicode
    ];

    for &ch in &test_chars {
        let s: String<E> = String::from(ch);
        assert_eq!(s.chars().next(), Some(ch), "failed for U+{:04X}", ch as u32);
    }
}

test_for_all_encodings!(test_roundtrip_supplementary);

// =============================================================================
// Ordering and Comparison Tests
// =============================================================================

fn test_ord<E: Encoding>() {
    let a: String<E> = make_string("a");
    let b: String<E> = make_string("b");
    let aa: String<E> = make_string("aa");

    assert!(a < b);
    assert!(a < aa);
    assert!(b > a);
}

test_for_all_encodings!(test_ord);

fn test_eq<E: Encoding>() {
    let s1: String<E> = make_string("hello");
    let s2: String<E> = make_string("hello");
    let s3: String<E> = make_string("world");

    assert_eq!(s1, s2);
    assert_ne!(s1, s3);
}

test_for_all_encodings!(test_eq);

// =============================================================================
// Conversion Tests
// =============================================================================

fn test_into_bytes<E: Encoding>() {
    let s: String<E> = make_string("hello");
    let bytes = s.into_bytes();
    assert!(!bytes.is_empty());
}

test_for_all_encodings!(test_into_bytes);

fn test_as_bytes<E: Encoding>() {
    let s: String<E> = make_string("hello");
    let bytes = s.as_bytes();
    assert!(!bytes.is_empty());
}

test_for_all_encodings!(test_as_bytes);

fn test_into_boxed_str<E: Encoding>() {
    let s: String<E> = make_string("hello");
    let boxed = s.into_boxed_str();
    assert!(str_eq(&*boxed, "hello"));
}

test_for_all_encodings!(test_into_boxed_str);

// =============================================================================
// UTF-8 Specific Tests
// =============================================================================

#[test]
fn test_utf8_from_str() {
    let s: String<Utf8> = String::from("hello");
    assert!(str_eq(&s, "hello"));

    let s: String<Utf8> = String::from("héllo 世界");
    assert!(str_eq(&s, "héllo 世界"));
}

#[test]
fn test_utf8_to_std_string() {
    let s: String<Utf8> = String::from("hello");
    let std_string: std::string::String = s.into();
    assert_eq!(std_string, "hello");
}

#[test]
fn test_utf8_from_std_string() {
    let std_string = std::string::String::from("hello");
    let s: String<Utf8> = String::from(std_string);
    assert!(str_eq(&s, "hello"));
}

#[test]
fn test_utf8_str_to_std_str() {
    let s: String<Utf8> = String::from("hello");
    let std_str: &str = (&*s).into();
    assert_eq!(std_str, "hello");
}

// =============================================================================
// Edge Cases
// =============================================================================

fn test_empty_string_operations<E: Encoding>() {
    let empty: String<E> = String::new();

    assert!(empty.is_empty());
    assert_eq!(empty.len(), 0);
    assert_eq!(empty.chars().count(), 0);
    assert_eq!(empty.chars().next(), None);
    assert!(empty.is_char_boundary(0));
    assert!(str_eq(empty.trim(), ""));

    let split: Vec<_> = empty.split(',').collect();
    assert_eq!(split.len(), 1); // Empty string splits into one empty part
}

test_for_all_encodings!(test_empty_string_operations);

fn test_single_char_string<E: Encoding>() {
    let s: String<E> = make_string("a");

    assert_eq!(s.chars().count(), 1);
    assert_eq!(s.chars().next(), Some('a'));
    assert_eq!(s.chars().last(), Some('a'));
    assert!(s.contains('a'));
    assert!(!s.contains('b'));
    assert!(s.starts_with('a'));
    assert!(s.ends_with('a'));
}

test_for_all_encodings!(test_single_char_string);

fn test_unicode_edge_cases<E: Encoding>() {
    // Zero-width joiner sequences (emoji modifiers)
    let family = "\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F467}"; // 👨‍👩‍👧
    let s: String<E> = make_string(family);
    // Should preserve all codepoints
    let chars: Vec<char> = s.chars().collect();
    assert!(chars.len() >= 5); // At least the base characters

    // Combining characters
    let combining = "e\u{0301}"; // e + combining acute accent
    let s: String<E> = make_string(combining);
    let chars: Vec<char> = s.chars().collect();
    assert_eq!(chars, vec!['e', '\u{0301}']);
}

test_for_all_encodings!(test_unicode_edge_cases);

// =============================================================================
// Pattern Trait Tests
// =============================================================================

fn test_pattern_predicate<E: Encoding>() {
    let s: String<E> = make_string("hello world");

    // Test contains with predicate
    assert!(s.contains(|c: char| c.is_whitespace()));
    assert!(!s.contains(|c: char| c.is_numeric()));

    // Test find with predicate
    assert!(s.find(|c: char| c.is_whitespace()).is_some());

    // Test split with predicate
    let parts: Vec<_> = s.split(|c: char| c.is_whitespace()).collect();
    assert_eq!(parts.len(), 2);

    // Test trim_matches with predicate
    let trimmed = s.trim_matches(|c: char| c == 'h' || c == 'd');
    assert!(str_eq(trimmed, "ello worl"));
}

test_for_all_encodings!(test_pattern_predicate);

fn test_pattern_char_slice<E: Encoding>() {
    let s: String<E> = make_string("hello, world!");
    let vowels: &[char] = &['a', 'e', 'i', 'o', 'u'];

    // Test contains with char slice
    assert!(s.contains(vowels));

    // Test find with char slice
    let pos = s.find(vowels);
    assert!(pos.is_some());

    // Test split with char slice
    let parts: Vec<_> = s.split(&[',', ' '][..]).collect();
    assert!(parts.len() > 1);

    // Test trim_matches with char slice
    let trimmed = s.trim_matches(&['h', '!'][..]);
    assert!(str_eq(trimmed, "ello, world"));
}

test_for_all_encodings!(test_pattern_char_slice);

fn test_pattern_str<E: Encoding>() {
    let s: String<E> = make_string("hello world hello");
    let pattern: String<E> = make_string("hello");

    // Test contains with &Str<E>
    assert!(s.contains(pattern.as_str()));

    // Test starts_with with &Str<E>
    assert!(s.starts_with(pattern.as_str()));

    // Test ends_with with &Str<E>
    assert!(s.ends_with(pattern.as_str()));

    // Test find with &Str<E>
    let pos = s.find(pattern.as_str());
    assert_eq!(pos, Some(0));
}

test_for_all_encodings!(test_pattern_str);

fn test_remove_matches_predicate<E: Encoding>() {
    let mut s: String<E> = make_string("h3ll0 w0rld");
    s.remove_matches(|c: char| c.is_numeric());
    assert!(str_eq(&s, "hll wrld"));
}

test_for_all_encodings!(test_remove_matches_predicate);

fn test_remove_matches_char_slice<E: Encoding>() {
    let mut s: String<E> = make_string("hello world");
    s.remove_matches(&['l', 'o'][..]);
    assert!(str_eq(&s, "he wrd"));
}

test_for_all_encodings!(test_remove_matches_char_slice);
