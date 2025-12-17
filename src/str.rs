use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ops::{
    Index, IndexMut, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
};
use core::str::FromStr;

use crate::String;
use crate::encoding::Encoding;
use crate::error::EncodingError;
use crate::iter::{
    Bytes, CharIndices, Chars, EscapeDebug, EscapeDefault, EscapeUnicode, Lines, MatchIndices,
    Matches, RMatchIndices, RMatches, RSplit, RSplitN, RSplitTerminator, Split,
    SplitAsciiWhitespace, SplitInclusive, SplitN, SplitTerminator, SplitWhitespace,
};
use crate::pattern::{DoubleEndedSearcher, Pattern, ReverseSearcher, SearchStep, Searcher};

/// A borrowed string slice in encoding `E`.
///
/// This is the borrowed counterpart to [`String<E>`], analogous to how
/// `str` relates to `std::string::String`.
#[repr(transparent)]
pub struct Str<E: Encoding> {
    _marker: PhantomData<E>,
    bytes: [u8],
}

impl<E: Encoding> Str<E> {
    // === Construction ===

    /// Converts a byte slice to a string slice.
    ///
    /// Returns an error if the bytes are not valid for this encoding.
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Result<&Self, EncodingError> {
        E::validate(bytes)?;
        Ok(unsafe { Self::from_bytes_unchecked(bytes) })
    }

    /// Converts a byte slice to a string slice without checking validity.
    ///
    /// # Safety
    ///
    /// The bytes must be valid for this encoding.
    #[inline]
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        // SAFETY: Caller guarantees bytes are valid for encoding E
        unsafe { &*(bytes as *const [u8] as *const Self) }
    }

    /// Converts a mutable byte slice to a mutable string slice.
    ///
    /// Returns an error if the bytes are not valid for this encoding.
    #[inline]
    pub fn from_bytes_mut(bytes: &mut [u8]) -> Result<&mut Self, EncodingError> {
        E::validate(bytes)?;
        Ok(unsafe { Self::from_bytes_unchecked_mut(bytes) })
    }

    /// Converts a mutable byte slice to a mutable string slice without checking validity.
    ///
    /// # Safety
    ///
    /// The bytes must be valid for this encoding.
    #[inline]
    pub unsafe fn from_bytes_unchecked_mut(bytes: &mut [u8]) -> &mut Self {
        // SAFETY: Caller guarantees bytes are valid for encoding E
        unsafe { &mut *(bytes as *mut [u8] as *mut Self) }
    }

    // === Length ===

    /// Returns the length of `self` in bytes.
    #[inline]
    pub const fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Returns `true` if `self` has a length of zero bytes.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    // === Validation ===

    /// Checks that `index`-th byte is the first byte in an encoded character
    /// sequence or the end of the string.
    #[inline]
    pub fn is_char_boundary(&self, index: usize) -> bool {
        if index == 0 || index == self.len() {
            true
        } else if index > self.len() {
            false
        } else {
            E::is_char_boundary(&self.bytes, index)
        }
    }

    /// Finds the closest char boundary at or before `index`.
    ///
    /// If `index` is greater than the length of the string, returns the length.
    ///
    /// # Examples
    ///
    /// ```
    /// use stringly::{String, Utf8};
    ///
    /// let s: String<Utf8> = "hello".chars().collect();
    /// assert_eq!(s.floor_char_boundary(3), 3);
    /// assert_eq!(s.floor_char_boundary(100), s.len());
    /// ```
    #[inline]
    pub fn floor_char_boundary(&self, index: usize) -> usize {
        if index >= self.len() {
            self.len()
        } else if self.is_char_boundary(index) {
            index
        } else {
            // Scan backwards to find a char boundary
            let mut i = index;
            while i > 0 && !self.is_char_boundary(i) {
                i -= 1;
            }
            i
        }
    }

    /// Finds the closest char boundary at or after `index`.
    ///
    /// If `index` is greater than the length of the string, returns the length.
    ///
    /// # Panics
    ///
    /// Panics if `index > self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stringly::{String, Utf8};
    ///
    /// let s: String<Utf8> = "hello".chars().collect();
    /// assert_eq!(s.ceil_char_boundary(3), 3);
    /// ```
    #[inline]
    pub fn ceil_char_boundary(&self, index: usize) -> usize {
        if index > self.len() {
            panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len(),
                index
            );
        }
        if self.is_char_boundary(index) {
            index
        } else {
            // Scan forwards to find a char boundary
            let mut i = index;
            while i < self.len() && !self.is_char_boundary(i) {
                i += 1;
            }
            i
        }
    }

    // === Byte access ===

    /// Converts a string slice to a byte slice.
    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Converts a mutable string slice to a mutable byte slice.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the content of the slice is valid
    /// for this encoding before returning.
    #[inline]
    pub unsafe fn as_bytes_mut(&mut self) -> &mut [u8] {
        &mut self.bytes
    }

    /// Converts a string slice to a raw pointer.
    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        self.bytes.as_ptr()
    }

    /// Converts a mutable string slice to a raw pointer.
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.bytes.as_mut_ptr()
    }

    // === Slicing ===

    /// Returns a subslice of `self`.
    ///
    /// Returns `None` if the range is out of bounds or not on character boundaries.
    #[inline]
    pub fn get(&self, range: Range<usize>) -> Option<&Self> {
        if range.start <= range.end
            && range.end <= self.len()
            && self.is_char_boundary(range.start)
            && self.is_char_boundary(range.end)
        {
            Some(unsafe { Self::from_bytes_unchecked(&self.bytes[range]) })
        } else {
            None
        }
    }

    /// Returns a mutable subslice of `self`.
    ///
    /// Returns `None` if the range is out of bounds or not on character boundaries.
    #[inline]
    pub fn get_mut(&mut self, range: Range<usize>) -> Option<&mut Self> {
        if range.start <= range.end
            && range.end <= self.len()
            && self.is_char_boundary(range.start)
            && self.is_char_boundary(range.end)
        {
            Some(unsafe { Self::from_bytes_unchecked_mut(&mut self.bytes[range]) })
        } else {
            None
        }
    }

    /// Returns a subslice of `self` without bounds checking.
    ///
    /// # Safety
    ///
    /// The range must be valid and on character boundaries.
    #[inline]
    pub unsafe fn get_unchecked(&self, range: Range<usize>) -> &Self {
        // SAFETY: Caller guarantees range is valid and on char boundaries
        unsafe { Self::from_bytes_unchecked(&self.bytes[range]) }
    }

    /// Returns a mutable subslice of `self` without bounds checking.
    ///
    /// # Safety
    ///
    /// The range must be valid and on character boundaries.
    #[inline]
    pub unsafe fn get_unchecked_mut(&mut self, range: Range<usize>) -> &mut Self {
        // SAFETY: Caller guarantees range is valid and on char boundaries
        unsafe { Self::from_bytes_unchecked_mut(&mut self.bytes[range]) }
    }

    // === Splitting at index ===

    /// Divides one string slice into two at an index.
    ///
    /// # Panics
    ///
    /// Panics if `mid` is not on a character boundary, or if it is past the end of the string.
    #[inline]
    pub fn split_at(&self, mid: usize) -> (&Self, &Self) {
        self.split_at_checked(mid)
            .expect("mid is not a char boundary or is out of bounds")
    }

    /// Divides one mutable string slice into two at an index.
    ///
    /// # Panics
    ///
    /// Panics if `mid` is not on a character boundary, or if it is past the end of the string.
    #[inline]
    pub fn split_at_mut(&mut self, mid: usize) -> (&mut Self, &mut Self) {
        self.split_at_mut_checked(mid)
            .expect("mid is not a char boundary or is out of bounds")
    }

    /// Divides one string slice into two at an index, returning `None` if
    /// the index is out of bounds or not on a character boundary.
    #[inline]
    pub fn split_at_checked(&self, mid: usize) -> Option<(&Self, &Self)> {
        if self.is_char_boundary(mid) {
            let (a, b) = self.bytes.split_at(mid);
            Some(unsafe { (Self::from_bytes_unchecked(a), Self::from_bytes_unchecked(b)) })
        } else {
            None
        }
    }

    /// Divides one mutable string slice into two at an index, returning `None` if
    /// the index is out of bounds or not on a character boundary.
    #[inline]
    pub fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut Self, &mut Self)> {
        if self.is_char_boundary(mid) {
            let (a, b) = self.bytes.split_at_mut(mid);
            Some(unsafe {
                (
                    Self::from_bytes_unchecked_mut(a),
                    Self::from_bytes_unchecked_mut(b),
                )
            })
        } else {
            None
        }
    }

    // === Character access ===

    /// Returns an iterator over the `char`s of a string slice.
    #[inline]
    pub fn chars(&self) -> Chars<'_, E> {
        Chars::new(self)
    }

    /// Returns an iterator over the `char`s of a string slice, and their positions.
    #[inline]
    pub fn char_indices(&self) -> CharIndices<'_, E> {
        CharIndices::new(self)
    }

    // === Byte iteration ===

    /// Returns an iterator over the bytes of a string slice.
    #[inline]
    pub fn bytes(&self) -> Bytes<'_> {
        Bytes::new(&self.bytes)
    }

    // === Whitespace/line splitting ===

    /// Splits a string slice by whitespace.
    #[inline]
    pub fn split_whitespace(&self) -> SplitWhitespace<'_, E> {
        SplitWhitespace::new(self)
    }

    /// Splits a string slice by ASCII whitespace.
    #[inline]
    pub fn split_ascii_whitespace(&self) -> SplitAsciiWhitespace<'_> {
        SplitAsciiWhitespace::new(&self.bytes)
    }

    /// Returns an iterator over the lines of a string, as string slices.
    #[inline]
    pub fn lines(&self) -> Lines<'_, E> {
        Lines::new(self)
    }

    // === Search ===

    /// Returns `true` if the given pattern matches somewhere in this string slice.
    #[inline]
    pub fn contains<'a, P: Pattern<'a, E>>(&'a self, pat: P) -> bool {
        pat.is_contained_in(self)
    }

    /// Returns `true` if the given pattern matches at the start of this string slice.
    #[inline]
    pub fn starts_with<'a, P: Pattern<'a, E>>(&'a self, pat: P) -> bool {
        pat.is_prefix_of(self)
    }

    /// Returns `true` if the given pattern matches at the end of this string slice.
    #[inline]
    pub fn ends_with<'a, P: Pattern<'a, E>>(&'a self, pat: P) -> bool
    where
        P::Searcher: ReverseSearcher<'a, E>,
    {
        pat.is_suffix_of(self)
    }

    /// Returns the byte index of the first match of the pattern.
    pub fn find<'a, P: Pattern<'a, E>>(&'a self, pat: P) -> Option<usize> {
        pat.into_searcher(self).next_match().map(|(i, _)| i)
    }

    /// Returns the byte index of the last match of the pattern.
    pub fn rfind<'a, P: Pattern<'a, E>>(&'a self, pat: P) -> Option<usize>
    where
        P::Searcher: ReverseSearcher<'a, E>,
    {
        pat.into_searcher(self).next_match_back().map(|(i, _)| i)
    }

    // === Split iterators ===

    /// An iterator over substrings of this string slice, separated by the given pattern.
    #[inline]
    pub fn split<'a, P: Pattern<'a, E>>(&'a self, pat: P) -> Split<'a, E, P::Searcher> {
        Split::new(pat.into_searcher(self))
    }

    /// An iterator over substrings of this string slice, separated by the given pattern.
    /// The matched pattern is included in the yielded substring.
    #[inline]
    pub fn split_inclusive<'a, P: Pattern<'a, E>>(
        &'a self,
        pat: P,
    ) -> SplitInclusive<'a, E, P::Searcher> {
        SplitInclusive::new(pat.into_searcher(self))
    }

    /// An iterator over substrings of this string slice, separated by the given pattern,
    /// starting from the end of the string.
    #[inline]
    pub fn rsplit<'a, P>(&'a self, pat: P) -> RSplit<'a, E, P::Searcher>
    where
        P: Pattern<'a, E, Searcher: ReverseSearcher<'a, E>>,
    {
        RSplit::new(pat.into_searcher(self))
    }

    /// An iterator over substrings of this string slice, separated by the given pattern,
    /// treating the pattern as a terminator rather than a separator.
    ///
    /// Unlike [`split`], this does not yield an empty string at the end
    /// if the string ends with the pattern.
    ///
    /// [`split`]: Self::split
    #[inline]
    pub fn split_terminator<'a, P: Pattern<'a, E>>(
        &'a self,
        pat: P,
    ) -> SplitTerminator<'a, E, P::Searcher> {
        SplitTerminator::new(pat.into_searcher(self))
    }

    /// An iterator over substrings of this string slice, separated by the given pattern,
    /// starting from the end, treating the pattern as a terminator.
    ///
    /// Unlike [`rsplit`], this does not yield an empty string at the start
    /// if the string ends with the pattern.
    ///
    /// [`rsplit`]: Self::rsplit
    #[inline]
    pub fn rsplit_terminator<'a, P>(&'a self, pat: P) -> RSplitTerminator<'a, E, P::Searcher>
    where
        P: Pattern<'a, E, Searcher: ReverseSearcher<'a, E>>,
    {
        RSplitTerminator::new(pat.into_searcher(self))
    }

    /// An iterator over substrings of this string slice, separated by the given pattern,
    /// restricted to returning at most `n` items.
    #[inline]
    pub fn splitn<'a, P: Pattern<'a, E>>(&'a self, n: usize, pat: P) -> SplitN<'a, E, P::Searcher> {
        SplitN::new(pat.into_searcher(self), n)
    }

    /// An iterator over substrings of this string slice, separated by the given pattern,
    /// starting from the end of the string, restricted to returning at most `n` items.
    #[inline]
    pub fn rsplitn<'a, P>(&'a self, n: usize, pat: P) -> RSplitN<'a, E, P::Searcher>
    where
        P: Pattern<'a, E, Searcher: ReverseSearcher<'a, E>>,
    {
        RSplitN::new(pat.into_searcher(self), n)
    }

    /// Splits the string on the first occurrence of the specified pattern
    /// and returns prefix before the match and suffix after the match.
    pub fn split_once<'a, P: Pattern<'a, E>>(&'a self, pat: P) -> Option<(&'a Self, &'a Self)> {
        let (start, end) = pat.into_searcher(self).next_match()?;
        Some(unsafe {
            (
                Self::from_bytes_unchecked(&self.bytes[..start]),
                Self::from_bytes_unchecked(&self.bytes[end..]),
            )
        })
    }

    /// Splits the string on the last occurrence of the specified pattern
    /// and returns prefix before the match and suffix after the match.
    pub fn rsplit_once<'a, P>(&'a self, pat: P) -> Option<(&'a Self, &'a Self)>
    where
        P: Pattern<'a, E, Searcher: ReverseSearcher<'a, E>>,
    {
        let (start, end) = pat.into_searcher(self).next_match_back()?;
        Some(unsafe {
            (
                Self::from_bytes_unchecked(&self.bytes[..start]),
                Self::from_bytes_unchecked(&self.bytes[end..]),
            )
        })
    }

    // === Match iterators ===

    /// An iterator over the disjoint matches of a pattern within this string slice.
    #[inline]
    pub fn matches<'a, P: Pattern<'a, E>>(&'a self, pat: P) -> Matches<'a, E, P::Searcher> {
        Matches::new(pat.into_searcher(self))
    }

    /// An iterator over the disjoint matches of a pattern within this string slice,
    /// yielded in reverse order.
    #[inline]
    pub fn rmatches<'a, P>(&'a self, pat: P) -> RMatches<'a, E, P::Searcher>
    where
        P: Pattern<'a, E, Searcher: ReverseSearcher<'a, E>>,
    {
        RMatches::new(pat.into_searcher(self))
    }

    /// An iterator over the disjoint matches of a pattern within this string slice,
    /// as well as their indices.
    #[inline]
    pub fn match_indices<'a, P: Pattern<'a, E>>(
        &'a self,
        pat: P,
    ) -> MatchIndices<'a, E, P::Searcher> {
        MatchIndices::new(pat.into_searcher(self))
    }

    /// An iterator over the disjoint matches of a pattern within this string slice,
    /// yielded in reverse order along with their indices.
    #[inline]
    pub fn rmatch_indices<'a, P>(&'a self, pat: P) -> RMatchIndices<'a, E, P::Searcher>
    where
        P: Pattern<'a, E, Searcher: ReverseSearcher<'a, E>>,
    {
        RMatchIndices::new(pat.into_searcher(self))
    }

    // === Trimming ===

    /// Returns a string slice with leading and trailing whitespace removed.
    #[inline]
    pub fn trim(&self) -> &Self {
        self.trim_start().trim_end()
    }

    /// Returns a string slice with leading whitespace removed.
    pub fn trim_start(&self) -> &Self {
        let mut offset = 0;
        while offset < self.len() {
            if let Some((c, next)) = E::decode_char_at(&self.bytes, offset) {
                if c.is_whitespace() {
                    offset = next;
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        unsafe { Self::from_bytes_unchecked(&self.bytes[offset..]) }
    }

    /// Returns a string slice with trailing whitespace removed.
    pub fn trim_end(&self) -> &Self {
        let mut end = self.len();
        while end > 0 {
            if let Some((c, start)) = E::decode_char_before(&self.bytes, end) {
                if c.is_whitespace() {
                    end = start;
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        unsafe { Self::from_bytes_unchecked(&self.bytes[..end]) }
    }

    /// Returns a string slice with all prefixes and suffixes that match the pattern repeatedly removed.
    #[inline]
    pub fn trim_matches<'a, P>(&'a self, pat: P) -> &'a Self
    where
        P: Pattern<'a, E, Searcher: DoubleEndedSearcher<'a, E>> + Clone,
    {
        self.trim_start_matches(pat.clone()).trim_end_matches(pat)
    }

    /// Returns a string slice with all prefixes that match the pattern repeatedly removed.
    pub fn trim_start_matches<'a, P: Pattern<'a, E>>(&'a self, pat: P) -> &'a Self {
        let mut searcher = pat.into_searcher(self);
        let mut offset = 0;
        loop {
            match searcher.next() {
                SearchStep::Match(a, b) if a == offset => {
                    offset = b;
                }
                SearchStep::Reject(_, _) => {
                    break unsafe { Self::from_bytes_unchecked(&self.bytes[offset..]) };
                }
                _ => break unsafe { Self::from_bytes_unchecked(&self.bytes[offset..]) },
            }
        }
    }

    /// Returns a string slice with all suffixes that match the pattern repeatedly removed.
    pub fn trim_end_matches<'a, P>(&'a self, pat: P) -> &'a Self
    where
        P: Pattern<'a, E, Searcher: ReverseSearcher<'a, E>>,
    {
        let mut searcher = pat.into_searcher(self);
        let mut end = self.len();
        loop {
            match searcher.next_back() {
                SearchStep::Match(a, b) if b == end => {
                    end = a;
                }
                SearchStep::Reject(_, _) => {
                    break unsafe { Self::from_bytes_unchecked(&self.bytes[..end]) };
                }
                _ => break unsafe { Self::from_bytes_unchecked(&self.bytes[..end]) },
            }
        }
    }

    /// Returns a string slice with the prefix removed.
    pub fn strip_prefix<'a, P: Pattern<'a, E>>(&'a self, pat: P) -> Option<&'a Self> {
        pat.strip_prefix_of(self)
    }

    /// Returns a string slice with the suffix removed.
    pub fn strip_suffix<'a, P>(&'a self, pat: P) -> Option<&'a Self>
    where
        P: Pattern<'a, E, Searcher: ReverseSearcher<'a, E>>,
    {
        pat.strip_suffix_of(self)
    }

    // === Parsing ===

    /// Parses this string slice into another type.
    #[inline]
    pub fn parse<F: FromStr>(&self) -> Result<F, F::Err> {
        // For parsing, we need to convert to a UTF-8 str first
        // This works for all encodings as we iterate chars
        let s: std::string::String = self.chars().collect();
        s.parse()
    }

    // === ASCII operations ===

    /// Checks if all characters in this string are within the ASCII range.
    #[inline]
    pub fn is_ascii(&self) -> bool {
        self.bytes.is_ascii()
    }

    /// Checks that two strings are an ASCII case-insensitive match.
    #[inline]
    pub fn eq_ignore_ascii_case(&self, other: &Self) -> bool {
        self.bytes.eq_ignore_ascii_case(&other.bytes)
    }

    /// Converts this string to its ASCII upper case equivalent in-place.
    #[inline]
    pub fn make_ascii_uppercase(&mut self) {
        self.bytes.make_ascii_uppercase()
    }

    /// Converts this string to its ASCII lower case equivalent in-place.
    #[inline]
    pub fn make_ascii_lowercase(&mut self) {
        self.bytes.make_ascii_lowercase()
    }

    /// Returns the lowercase equivalent of this string slice, as a new `String<E>`.
    pub fn to_lowercase(&self) -> String<E> {
        let mut result = String::new();
        for c in self.chars() {
            for lower in c.to_lowercase() {
                result.push(lower);
            }
        }
        result
    }

    /// Returns the uppercase equivalent of this string slice, as a new `String<E>`.
    pub fn to_uppercase(&self) -> String<E> {
        let mut result = String::new();
        for c in self.chars() {
            for upper in c.to_uppercase() {
                result.push(upper);
            }
        }
        result
    }

    /// Returns the lowercase ASCII equivalent of this string slice, as a new `String<E>`.
    pub fn to_ascii_lowercase(&self) -> String<E> {
        let mut result = String::with_capacity(self.len());
        for c in self.chars() {
            result.push(c.to_ascii_lowercase());
        }
        result
    }

    /// Returns the uppercase ASCII equivalent of this string slice, as a new `String<E>`.
    pub fn to_ascii_uppercase(&self) -> String<E> {
        let mut result = String::with_capacity(self.len());
        for c in self.chars() {
            result.push(c.to_ascii_uppercase());
        }
        result
    }

    // === Escaping ===

    /// Return an iterator that escapes each char in `self` with [`char::escape_debug`].
    ///
    /// # Examples
    ///
    /// ```
    /// use stringly::{String, Utf8};
    ///
    /// let s: String<Utf8> = "hello\tworld".chars().collect();
    /// let escaped: std::string::String = s.escape_debug().collect();
    /// assert_eq!(escaped, "hello\\tworld");
    /// ```
    #[inline]
    pub fn escape_debug(&self) -> EscapeDebug<'_, E> {
        EscapeDebug::new(self)
    }

    /// Return an iterator that escapes each char in `self` with [`char::escape_default`].
    ///
    /// # Examples
    ///
    /// ```
    /// use stringly::{String, Utf8};
    ///
    /// let s: String<Utf8> = "hello\tworld".chars().collect();
    /// let escaped: std::string::String = s.escape_default().collect();
    /// assert_eq!(escaped, "hello\\tworld");
    /// ```
    #[inline]
    pub fn escape_default(&self) -> EscapeDefault<'_, E> {
        EscapeDefault::new(self)
    }

    /// Return an iterator that escapes each char in `self` with [`char::escape_unicode`].
    ///
    /// # Examples
    ///
    /// ```
    /// use stringly::{String, Utf8};
    ///
    /// let s: String<Utf8> = "ab".chars().collect();
    /// let escaped: std::string::String = s.escape_unicode().collect();
    /// assert_eq!(escaped, "\\u{61}\\u{62}");
    /// ```
    #[inline]
    pub fn escape_unicode(&self) -> EscapeUnicode<'_, E> {
        EscapeUnicode::new(self)
    }

    // === Other ===

    /// Creates a new `String<E>` by repeating a string `n` times.
    pub fn repeat(&self, n: usize) -> String<E> {
        let mut result = String::with_capacity(self.len().saturating_mul(n));
        for _ in 0..n {
            result.push_str(self);
        }
        result
    }

    /// Replaces all matches of a character with another string.
    pub fn replace(&self, from: char, to: &Self) -> String<E> {
        let mut result = String::new();
        let mut last_end = 0;

        for (start, _) in self.char_indices().filter(|(_, c)| *c == from) {
            result.push_str(unsafe { Self::from_bytes_unchecked(&self.bytes[last_end..start]) });
            result.push_str(to);
            last_end = start + E::encoded_len(from);
        }
        result.push_str(unsafe { Self::from_bytes_unchecked(&self.bytes[last_end..]) });
        result
    }

    /// Replaces first N matches of a character with another string.
    pub fn replacen(&self, from: char, to: &Self, count: usize) -> String<E> {
        let mut result = String::new();
        let mut last_end = 0;
        let mut remaining = count;

        for (start, _) in self.char_indices().filter(|(_, c)| *c == from) {
            if remaining == 0 {
                break;
            }
            result.push_str(unsafe { Self::from_bytes_unchecked(&self.bytes[last_end..start]) });
            result.push_str(to);
            last_end = start + E::encoded_len(from);
            remaining -= 1;
        }
        result.push_str(unsafe { Self::from_bytes_unchecked(&self.bytes[last_end..]) });
        result
    }
}

// === Trait implementations ===

impl<E: Encoding> ToOwned for Str<E> {
    type Owned = String<E>;

    fn to_owned(&self) -> String<E> {
        String::from(self)
    }
}

impl<E: Encoding> fmt::Debug for Str<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"")?;
        for c in self.chars() {
            for c in c.escape_debug() {
                write!(f, "{}", c)?;
            }
        }
        write!(f, "\"")
    }
}

impl<E: Encoding> fmt::Display for Str<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for c in self.chars() {
            write!(f, "{}", c)?;
        }
        Ok(())
    }
}

impl<E: Encoding> Hash for Str<E> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes.hash(state)
    }
}

impl<E: Encoding> PartialEq for Str<E> {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}

impl<E: Encoding> Eq for Str<E> {}

impl<E: Encoding> PartialOrd for Str<E> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<E: Encoding> Ord for Str<E> {
    fn cmp(&self, other: &Self) -> Ordering {
        // Compare by character sequence for correctness
        self.chars().cmp(other.chars())
    }
}

impl<E: Encoding> AsRef<[u8]> for Str<E> {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl<E: Encoding> AsRef<Str<E>> for Str<E> {
    fn as_ref(&self) -> &Str<E> {
        self
    }
}

impl<E: Encoding> Default for &Str<E> {
    fn default() -> Self {
        // SAFETY: Empty byte slice is valid for all encodings
        unsafe { Str::from_bytes_unchecked(&[]) }
    }
}

impl<E: Encoding> Default for &mut Str<E> {
    fn default() -> Self {
        // SAFETY: Empty byte slice is valid for all encodings
        unsafe { Str::from_bytes_unchecked_mut(&mut []) }
    }
}

// === Index implementations ===

impl<E: Encoding> Index<RangeFull> for Str<E> {
    type Output = Str<E>;

    fn index(&self, _: RangeFull) -> &Self::Output {
        self
    }
}

impl<E: Encoding> Index<Range<usize>> for Str<E> {
    type Output = Str<E>;

    fn index(&self, index: Range<usize>) -> &Self::Output {
        self.get(index.clone()).unwrap_or_else(|| {
            panic!(
                "byte index {}..{} is out of bounds or not on char boundaries",
                index.start, index.end
            )
        })
    }
}

impl<E: Encoding> Index<RangeFrom<usize>> for Str<E> {
    type Output = Str<E>;

    fn index(&self, index: RangeFrom<usize>) -> &Self::Output {
        self.get(index.start..self.len()).unwrap_or_else(|| {
            panic!(
                "byte index {}.. is out of bounds or not on a char boundary",
                index.start
            )
        })
    }
}

impl<E: Encoding> Index<RangeTo<usize>> for Str<E> {
    type Output = Str<E>;

    fn index(&self, index: RangeTo<usize>) -> &Self::Output {
        self.get(0..index.end).unwrap_or_else(|| {
            panic!(
                "byte index ..{} is out of bounds or not on a char boundary",
                index.end
            )
        })
    }
}

impl<E: Encoding> Index<RangeInclusive<usize>> for Str<E> {
    type Output = Str<E>;

    fn index(&self, index: RangeInclusive<usize>) -> &Self::Output {
        let start = *index.start();
        let end = index.end().checked_add(1).expect("range end overflow");
        self.get(start..end).unwrap_or_else(|| {
            panic!(
                "byte index {}..={} is out of bounds or not on char boundaries",
                start,
                index.end()
            )
        })
    }
}

impl<E: Encoding> Index<RangeToInclusive<usize>> for Str<E> {
    type Output = Str<E>;

    fn index(&self, index: RangeToInclusive<usize>) -> &Self::Output {
        let end = index.end.checked_add(1).expect("range end overflow");
        self.get(0..end).unwrap_or_else(|| {
            panic!(
                "byte index ..={} is out of bounds or not on a char boundary",
                index.end
            )
        })
    }
}

impl<E: Encoding> IndexMut<RangeFull> for Str<E> {
    fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
        self
    }
}

impl<E: Encoding> IndexMut<Range<usize>> for Str<E> {
    fn index_mut(&mut self, index: Range<usize>) -> &mut Self::Output {
        self.get_mut(index.clone()).unwrap_or_else(|| {
            panic!(
                "byte index {}..{} is out of bounds or not on char boundaries",
                index.start, index.end
            )
        })
    }
}

impl<E: Encoding> IndexMut<RangeFrom<usize>> for Str<E> {
    fn index_mut(&mut self, index: RangeFrom<usize>) -> &mut Self::Output {
        let len = self.len();
        self.get_mut(index.start..len).unwrap_or_else(|| {
            panic!(
                "byte index {}.. is out of bounds or not on a char boundary",
                index.start
            )
        })
    }
}

impl<E: Encoding> IndexMut<RangeTo<usize>> for Str<E> {
    fn index_mut(&mut self, index: RangeTo<usize>) -> &mut Self::Output {
        self.get_mut(0..index.end).unwrap_or_else(|| {
            panic!(
                "byte index ..{} is out of bounds or not on a char boundary",
                index.end
            )
        })
    }
}

impl<E: Encoding> IndexMut<RangeInclusive<usize>> for Str<E> {
    fn index_mut(&mut self, index: RangeInclusive<usize>) -> &mut Self::Output {
        let start = *index.start();
        let end = index.end().checked_add(1).expect("range end overflow");
        self.get_mut(start..end).unwrap_or_else(|| {
            panic!(
                "byte index {}..={} is out of bounds or not on char boundaries",
                start,
                index.end()
            )
        })
    }
}

impl<E: Encoding> IndexMut<RangeToInclusive<usize>> for Str<E> {
    fn index_mut(&mut self, index: RangeToInclusive<usize>) -> &mut Self::Output {
        let end = index.end.checked_add(1).expect("range end overflow");
        self.get_mut(0..end).unwrap_or_else(|| {
            panic!(
                "byte index ..={} is out of bounds or not on a char boundary",
                index.end
            )
        })
    }
}
