use crate::Str;
use crate::String;
use crate::encoding::Encoding;
use crate::error::EncodingError;

/// UTF-8 encoding marker.
///
/// This is a zero-sized type that implements [`Encoding`] by delegating
/// to the standard library's UTF-8 string functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Utf8;

impl Encoding for Utf8 {
    const NAME: &'static str = "UTF-8";
    const IS_FIXED_WIDTH: bool = false;
    const BYTES_PER_CHAR: Option<usize> = None;
    const MAX_CHAR_LEN: usize = 4;

    #[inline]
    fn validate(bytes: &[u8]) -> Result<(), EncodingError> {
        match core::str::from_utf8(bytes) {
            Ok(_) => Ok(()),
            Err(e) => Err(EncodingError::new(e.valid_up_to(), e.error_len())),
        }
    }

    #[inline]
    fn decode_char_at(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        if offset >= bytes.len() {
            return None;
        }

        // SAFETY: We validate that offset is within bounds
        let slice = &bytes[offset..];

        // Get the first byte to determine character length
        let first = slice.first()?;
        let len = match first {
            0x00..=0x7F => 1,
            0xC0..=0xDF => 2,
            0xE0..=0xEF => 3,
            0xF0..=0xF7 => 4,
            _ => return None, // Invalid start byte
        };

        if slice.len() < len {
            return None;
        }

        // Validate and decode
        let char_bytes = &slice[..len];
        let s = core::str::from_utf8(char_bytes).ok()?;
        let c = s.chars().next()?;

        Some((c, offset + len))
    }

    #[inline]
    fn encoded_len(c: char) -> usize {
        c.len_utf8()
    }

    #[inline]
    fn encode_char(c: char, buf: &mut [u8]) -> usize {
        c.encode_utf8(buf).len()
    }

    #[inline]
    fn is_char_boundary(bytes: &[u8], index: usize) -> bool {
        if index == 0 || index >= bytes.len() {
            return true;
        }
        // UTF-8 continuation bytes have the pattern 10xxxxxx
        // A char boundary is any byte that is NOT a continuation byte
        !is_utf8_continuation(bytes[index])
    }

    fn decode_char_before(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        if offset == 0 || offset > bytes.len() {
            return None;
        }

        // UTF-8 is self-synchronizing, so we can scan backwards
        let mut start = offset - 1;
        while start > 0 && is_utf8_continuation(bytes[start]) {
            start -= 1;
        }

        // Validate the character
        let char_bytes = &bytes[start..offset];
        let s = core::str::from_utf8(char_bytes).ok()?;
        let c = s.chars().next()?;

        Some((c, start))
    }
}

/// Returns true if the byte is a UTF-8 continuation byte (10xxxxxx).
#[inline]
fn is_utf8_continuation(b: u8) -> bool {
    (b & 0xC0) == 0x80
}

// === Conversions from/to standard library str ===

impl From<&str> for String<Utf8> {
    /// Creates a `String<Utf8>` from a `&str`.
    ///
    /// Since `&str` is already valid UTF-8, this is a simple copy.
    #[inline]
    fn from(s: &str) -> Self {
        // SAFETY: &str is always valid UTF-8
        unsafe { String::from_bytes_unchecked(s.as_bytes().to_vec()) }
    }
}

impl From<std::string::String> for String<Utf8> {
    /// Creates a `String<Utf8>` from a `std::string::String`.
    #[inline]
    fn from(s: std::string::String) -> Self {
        // SAFETY: std::string::String is always valid UTF-8
        unsafe { String::from_bytes_unchecked(s.into_bytes()) }
    }
}

impl<'a> From<&'a Str<Utf8>> for &'a str {
    /// Converts a `&Str<Utf8>` to a `&str`.
    ///
    /// This is a zero-cost conversion since both are UTF-8.
    #[inline]
    fn from(s: &'a Str<Utf8>) -> &'a str {
        // SAFETY: Str<Utf8> is always valid UTF-8
        unsafe { std::str::from_utf8_unchecked(s.as_bytes()) }
    }
}

impl From<String<Utf8>> for std::string::String {
    /// Converts a `String<Utf8>` to a `std::string::String`.
    #[inline]
    fn from(s: String<Utf8>) -> std::string::String {
        // SAFETY: String<Utf8> is always valid UTF-8
        unsafe { std::string::String::from_utf8_unchecked(s.into_bytes()) }
    }
}

// === Str<Utf8> convenience methods ===

impl Str<Utf8> {
    /// Returns this string slice as a `&str`.
    ///
    /// This is a zero-cost conversion since both types are UTF-8.
    #[inline]
    pub fn as_std(&self) -> &str {
        // SAFETY: Str<Utf8> is always valid UTF-8
        unsafe { std::str::from_utf8_unchecked(self.as_bytes()) }
    }
}

// === AsRef<str> implementations ===

impl AsRef<str> for Str<Utf8> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_std()
    }
}

impl AsRef<str> for String<Utf8> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_std()
    }
}

// === Box<str> conversions ===

impl From<Box<str>> for String<Utf8> {
    /// Creates a `String<Utf8>` from a `Box<str>`.
    #[inline]
    fn from(s: Box<str>) -> Self {
        // SAFETY: Box<str> is always valid UTF-8
        unsafe { String::from_bytes_unchecked(s.into_string().into_bytes()) }
    }
}

impl From<String<Utf8>> for Box<str> {
    /// Converts a `String<Utf8>` to a `Box<str>`.
    #[inline]
    fn from(s: String<Utf8>) -> Box<str> {
        std::string::String::from(s).into_boxed_str()
    }
}

// === Cow<str> conversions ===

impl<'a> From<std::borrow::Cow<'a, str>> for String<Utf8> {
    /// Creates a `String<Utf8>` from a `Cow<str>`.
    #[inline]
    fn from(s: std::borrow::Cow<'a, str>) -> Self {
        // SAFETY: Cow<str> is always valid UTF-8
        unsafe { String::from_bytes_unchecked(s.into_owned().into_bytes()) }
    }
}

impl From<String<Utf8>> for std::borrow::Cow<'static, str> {
    /// Converts a `String<Utf8>` to a `Cow<'static, str>`.
    #[inline]
    fn from(s: String<Utf8>) -> std::borrow::Cow<'static, str> {
        std::borrow::Cow::Owned(std::string::String::from(s))
    }
}

impl crate::encoding::UniversalEncoding for Utf8 {}

// === Registry registration ===

#[cfg(feature = "registry")]
inventory::submit! {
    crate::registry::EncodingEntry {
        name: "UTF-8",
        aliases: &["UTF8", "utf-8", "utf8"],
        is_unicode: true,
        decode: |bytes| {
            Utf8::validate(bytes)?;
            let s = unsafe { std::str::from_utf8_unchecked(bytes) };
            Ok(s.chars().collect())
        },
        try_encode_char: |c| {
            let mut buf = [0u8; 4];
            let len = c.encode_utf8(&mut buf).len();
            Some(buf[..len].to_vec())
        },
    }
}

// === &str as Pattern for Str<Utf8> ===

use crate::pattern::{DoubleEndedSearcher, Pattern, ReverseSearcher, SearchStep, Searcher};

/// Searcher for a `&str` pattern in a `Str<Utf8>`.
pub struct StdStrSearcher<'a, 'b> {
    haystack: &'a Str<Utf8>,
    needle: &'b str,
    offset: usize,
    back_offset: usize,
    /// Flag to track completion of empty needle forward search
    empty_needle_done: bool,
    /// Flag to track completion of empty needle backward search
    empty_needle_done_back: bool,
}

impl<'a, 'b> StdStrSearcher<'a, 'b> {
    fn new(haystack: &'a Str<Utf8>, needle: &'b str) -> Self {
        Self {
            haystack,
            needle,
            offset: 0,
            back_offset: haystack.len(),
            empty_needle_done: false,
            empty_needle_done_back: false,
        }
    }
}

impl<'a, 'b> Searcher<'a, Utf8> for StdStrSearcher<'a, 'b> {
    fn haystack(&self) -> &'a Str<Utf8> {
        self.haystack
    }

    fn remainder(&self) -> &'a Str<Utf8> {
        unsafe {
            Str::from_bytes_unchecked(&self.haystack.as_bytes()[self.offset..self.back_offset])
        }
    }

    fn consumed(&self) -> usize {
        self.offset
    }

    fn next(&mut self) -> SearchStep {
        let hay = self.haystack.as_bytes();
        let needle = self.needle.as_bytes();
        let needle_len = needle.len();

        // Empty needle: match at every character boundary
        if needle_len == 0 {
            if self.empty_needle_done {
                return SearchStep::Done;
            }
            if self.offset < self.back_offset {
                let pos = self.offset;
                // Move to next char boundary
                if let Some((_, next)) = Utf8::decode_char_at(hay, self.offset) {
                    self.offset = next;
                } else {
                    self.offset = self.back_offset;
                }
                return SearchStep::Match(pos, pos);
            } else if self.offset == self.back_offset {
                self.empty_needle_done = true;
                return SearchStep::Match(self.offset, self.offset);
            }
            return SearchStep::Done;
        }

        if self.offset + needle_len > self.back_offset {
            if self.offset < self.back_offset {
                let old = self.offset;
                self.offset = self.back_offset;
                return SearchStep::Reject(old, self.back_offset);
            }
            return SearchStep::Done;
        }

        // Search for needle
        let search_end = self.back_offset - needle_len + 1;
        for i in self.offset..search_end {
            if &hay[i..i + needle_len] == needle {
                // Found a match - first reject any bytes before it
                if i > self.offset {
                    let old = self.offset;
                    self.offset = i;
                    return SearchStep::Reject(old, i);
                }
                // Return the match
                self.offset = i + needle_len;
                return SearchStep::Match(i, i + needle_len);
            }
        }

        // No match found, reject remaining
        if self.offset < self.back_offset {
            let old = self.offset;
            self.offset = self.back_offset;
            return SearchStep::Reject(old, self.back_offset);
        }

        SearchStep::Done
    }
}

impl<'a, 'b> ReverseSearcher<'a, Utf8> for StdStrSearcher<'a, 'b> {
    fn next_back(&mut self) -> SearchStep {
        let hay = self.haystack.as_bytes();
        let needle = self.needle.as_bytes();
        let needle_len = needle.len();

        // Empty needle: match at every character boundary (from back)
        if needle_len == 0 {
            if self.empty_needle_done_back {
                return SearchStep::Done;
            }
            if self.back_offset > self.offset {
                let pos = self.back_offset;
                // Move to previous char boundary
                let bytes = &hay[..self.back_offset];
                if let Some((_, prev)) = Utf8::decode_char_before(bytes, self.back_offset) {
                    self.back_offset = prev;
                } else {
                    self.back_offset = self.offset;
                }
                return SearchStep::Match(pos, pos);
            } else if self.back_offset == self.offset {
                self.empty_needle_done_back = true;
                return SearchStep::Match(self.offset, self.offset);
            }
            return SearchStep::Done;
        }

        if self.back_offset < self.offset + needle_len {
            if self.back_offset > self.offset {
                let old = self.back_offset;
                self.back_offset = self.offset;
                return SearchStep::Reject(self.offset, old);
            }
            return SearchStep::Done;
        }

        // Search backwards for needle
        let mut i = self.back_offset - needle_len;
        loop {
            if &hay[i..i + needle_len] == needle {
                // Found a match - first reject any bytes after it
                let end = i + needle_len;
                if end < self.back_offset {
                    let old = self.back_offset;
                    self.back_offset = end;
                    return SearchStep::Reject(end, old);
                }
                // Return the match
                self.back_offset = i;
                return SearchStep::Match(i, end);
            }
            if i == self.offset {
                break;
            }
            i -= 1;
        }

        // No match found, reject remaining
        if self.back_offset > self.offset {
            let old = self.back_offset;
            self.back_offset = self.offset;
            return SearchStep::Reject(self.offset, old);
        }

        SearchStep::Done
    }
}

impl<'a, 'b> DoubleEndedSearcher<'a, Utf8> for StdStrSearcher<'a, 'b> {}

impl<'a, 'b> Pattern<'a, Utf8> for &'b str {
    type Searcher = StdStrSearcher<'a, 'b>;

    fn into_searcher(self, haystack: &'a Str<Utf8>) -> Self::Searcher {
        StdStrSearcher::new(haystack, self)
    }

    fn is_contained_in(self, haystack: &'a Str<Utf8>) -> bool {
        if self.is_empty() {
            return true;
        }
        let needle = self.as_bytes();
        let hay = haystack.as_bytes();
        hay.windows(needle.len()).any(|w| w == needle)
    }

    fn is_prefix_of(self, haystack: &'a Str<Utf8>) -> bool {
        haystack.as_bytes().starts_with(self.as_bytes())
    }

    fn is_suffix_of(self, haystack: &'a Str<Utf8>) -> bool {
        haystack.as_bytes().ends_with(self.as_bytes())
    }
}

impl<'a, 'b, 'c> Pattern<'a, Utf8> for &'c &'b str {
    type Searcher = StdStrSearcher<'a, 'b>;

    fn into_searcher(self, haystack: &'a Str<Utf8>) -> Self::Searcher {
        (*self).into_searcher(haystack)
    }

    fn is_contained_in(self, haystack: &'a Str<Utf8>) -> bool {
        (*self).is_contained_in(haystack)
    }

    fn is_prefix_of(self, haystack: &'a Str<Utf8>) -> bool {
        (*self).is_prefix_of(haystack)
    }

    fn is_suffix_of(self, haystack: &'a Str<Utf8>) -> bool {
        (*self).is_suffix_of(haystack)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validate() {
        assert!(Utf8::validate(b"hello").is_ok());
        assert!(Utf8::validate("héllo".as_bytes()).is_ok());
        assert!(Utf8::validate("日本語".as_bytes()).is_ok());
        assert!(Utf8::validate(&[0xFF]).is_err());
        assert!(Utf8::validate(&[0xC0]).is_err()); // Incomplete sequence
    }

    #[test]
    fn test_decode_char_at() {
        let s = "héllo";
        let bytes = s.as_bytes();

        let (c, next) = Utf8::decode_char_at(bytes, 0).unwrap();
        assert_eq!(c, 'h');
        assert_eq!(next, 1);

        let (c, next) = Utf8::decode_char_at(bytes, 1).unwrap();
        assert_eq!(c, 'é');
        assert_eq!(next, 3);

        let (c, _) = Utf8::decode_char_at(bytes, 3).unwrap();
        assert_eq!(c, 'l');
    }

    #[test]
    fn test_decode_char_before() {
        let s = "héllo";
        let bytes = s.as_bytes();

        let (c, start) = Utf8::decode_char_before(bytes, bytes.len()).unwrap();
        assert_eq!(c, 'o');
        assert_eq!(start, bytes.len() - 1);

        let (c, start) = Utf8::decode_char_before(bytes, 3).unwrap();
        assert_eq!(c, 'é');
        assert_eq!(start, 1);
    }

    #[test]
    fn test_is_char_boundary() {
        let s = "héllo";
        let bytes = s.as_bytes();

        assert!(Utf8::is_char_boundary(bytes, 0));
        assert!(Utf8::is_char_boundary(bytes, 1));
        assert!(!Utf8::is_char_boundary(bytes, 2)); // Middle of 'é'
        assert!(Utf8::is_char_boundary(bytes, 3));
    }

    #[test]
    fn test_encode_char() {
        let mut buf = [0u8; 4];

        let len = Utf8::encode_char('h', &mut buf);
        assert_eq!(len, 1);
        assert_eq!(&buf[..len], b"h");

        let len = Utf8::encode_char('é', &mut buf);
        assert_eq!(len, 2);
        assert_eq!(&buf[..len], "é".as_bytes());

        let len = Utf8::encode_char('日', &mut buf);
        assert_eq!(len, 3);
        assert_eq!(&buf[..len], "日".as_bytes());
    }

    #[test]
    fn test_str_pattern() {
        let s: String<Utf8> = String::from("hello world");

        // Basic contains
        assert!(s.contains("hello"));
        assert!(s.contains("world"));
        assert!(s.contains("lo wo"));
        assert!(!s.contains("xyz"));

        // starts_with / ends_with
        assert!(s.starts_with("hello"));
        assert!(s.starts_with(""));
        assert!(!s.starts_with("world"));
        assert!(s.ends_with("world"));
        assert!(s.ends_with(""));
        assert!(!s.ends_with("hello"));

        // split
        let parts: Vec<_> = s.split(" ").collect();
        assert_eq!(parts.len(), 2);

        // split by longer pattern
        let s2: String<Utf8> = String::from("foo::bar::baz");
        let parts: Vec<_> = s2.split("::").collect();
        assert_eq!(parts.len(), 3);

        // rsplit
        let parts: Vec<_> = s2.rsplit("::").collect();
        assert_eq!(parts.len(), 3);

        // find
        assert_eq!(s.find("world"), Some(6));
        assert_eq!(s.find("xyz"), None);

        // rfind
        let s3: String<Utf8> = String::from("abcabc");
        assert_eq!(s3.rfind("bc"), Some(4));
        assert_eq!(s3.rfind("abc"), Some(3));

        // matches
        let count = s3.matches("bc").count();
        assert_eq!(count, 2);

        // Unicode
        let s4: String<Utf8> = String::from("héllo wörld");
        assert!(s4.contains("héllo"));
        assert!(s4.starts_with("héllo"));
        assert!(s4.ends_with("wörld"));
    }

    #[test]
    fn test_additional_pattern_types() {
        let s: String<Utf8> = String::from("hello world");

        // &&str pattern
        let pattern: &str = "wor";
        assert!(s.contains(&pattern));
        assert!(s.starts_with(&"hello"));
        assert!(s.ends_with(&"world"));

        // &String<Utf8> pattern
        let needle: String<Utf8> = String::from("world");
        assert!(s.contains(&needle));
        assert!(s.ends_with(&needle));

        // [char; N] pattern (owned array)
        assert!(s.contains(['a', 'e', 'i', 'o', 'u']));
        assert!(s.starts_with(['h', 'w']));

        // &[char; N] pattern
        let vowels = ['a', 'e', 'i', 'o', 'u'];
        assert!(s.contains(&vowels));
        assert!(s.starts_with(&['h', 'x']));

        // Split with [char; N]
        let parts: Vec<_> = s.split([' ']).collect();
        assert_eq!(parts.len(), 2);
    }

    #[test]
    fn test_from_str_trait() {
        use core::str::FromStr;

        // Test FromStr for String<Utf8>
        let s: String<Utf8> = "hello world".parse().unwrap();
        assert_eq!(s.len(), 11);

        // Test with unicode
        let s: String<Utf8> = "héllo wörld".parse().unwrap();
        assert!(s.chars().any(|c| c == 'é'));
    }

    #[test]
    fn test_double_ended_iterators() {
        let s: String<Utf8> = String::from("line1\nline2\nline3");

        // Lines: forward
        let lines: Vec<_> = s.lines().collect();
        assert_eq!(lines.len(), 3);

        // Lines: backward
        let lines_rev: Vec<_> = s.lines().rev().collect();
        assert_eq!(lines_rev.len(), 3);
        // Note: the order should be reversed

        // SplitWhitespace: forward
        let s2: String<Utf8> = String::from("  hello   world  ");
        let words: Vec<_> = s2.split_whitespace().collect();
        assert_eq!(words.len(), 2);

        // SplitWhitespace: backward
        let words_rev: Vec<_> = s2.split_whitespace().rev().collect();
        assert_eq!(words_rev.len(), 2);
    }
}
