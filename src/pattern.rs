//! Pattern matching for strings.
//!
//! This module provides the [`Pattern`] trait and associated types for searching
//! within strings. Patterns can be:
//!
//! - A single [`char`]
//! - A [`&str`] (for UTF-8 strings)
//! - A [`&Str<E>`](crate::Str) (substring of same encoding)
//! - A character predicate `FnMut(char) -> bool`
//! - A slice of characters `&[char]`
//!
//! # Examples
//!
//! ```
//! use stringly::{String, Utf8};
//!
//! let s: String<Utf8> = String::from("hello world");
//!
//! // Search for a character
//! assert!(s.contains('o'));
//!
//! // Search for a substring (UTF-8 supports &str patterns)
//! assert!(s.contains("wor"));
//! assert!(s.starts_with("hello"));
//! assert!(s.ends_with("world"));
//!
//! // Search with a predicate
//! assert!(s.contains(|c: char| c.is_whitespace()));
//!
//! // Search for any of several characters
//! assert!(s.contains(['a', 'e', 'i', 'o', 'u'].as_slice()));
//!
//! // Split by pattern
//! let words: Vec<_> = s.split(' ').collect();
//! assert_eq!(words.len(), 2);
//!
//! // Split by string
//! let parts: Vec<_> = s.split(" ").collect();
//! assert_eq!(parts.len(), 2);
//! ```
//!
//! # Searcher Protocol
//!
//! The [`Searcher`] trait provides low-level access to pattern matching:
//!
//! ```
//! use stringly::{String, Utf8, Pattern, Searcher, SearchStep};
//!
//! let s: String<Utf8> = String::from("aaa");
//! let mut searcher = 'a'.into_searcher(&s);
//!
//! // Each call to next() returns a Match or Reject
//! assert_eq!(searcher.next(), SearchStep::Match(0, 1));
//! assert_eq!(searcher.next(), SearchStep::Match(1, 2));
//! assert_eq!(searcher.next(), SearchStep::Match(2, 3));
//! assert_eq!(searcher.next(), SearchStep::Done);
//! ```

use crate::Str;
use crate::encoding::Encoding;

/// Result of calling `Searcher::next()` or `ReverseSearcher::next_back()`.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SearchStep {
    /// Expresses that a match of the pattern has been found at
    /// `haystack[a..b]`.
    Match(usize, usize),
    /// Expresses that `haystack[a..b]` has been rejected as a possible match
    /// of the pattern.
    Reject(usize, usize),
    /// Expresses that every byte of the haystack has been visited.
    Done,
}

/// A searcher for a string pattern.
///
/// This trait provides methods for searching through a string haystack
/// for occurrences of a pattern.
pub trait Searcher<'a, E: Encoding> {
    /// Getter for the underlying string to be searched in.
    fn haystack(&self) -> &'a Str<E>;

    /// Returns the remainder of the haystack that hasn't been searched yet.
    fn remainder(&self) -> &'a Str<E>;

    /// Returns how many bytes have been consumed from the front.
    fn consumed(&self) -> usize;

    /// Performs the next search step starting from the front.
    fn next(&mut self) -> SearchStep;

    /// Finds the next `Match` result and returns the start and end indices.
    #[inline]
    fn next_match(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next() {
                SearchStep::Match(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                SearchStep::Reject(_, _) => continue,
            }
        }
    }

    /// Finds the next `Reject` result and returns the start and end indices.
    #[inline]
    fn next_reject(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next() {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                SearchStep::Match(_, _) => continue,
            }
        }
    }
}

/// A reverse searcher for a string pattern.
///
/// This trait provides methods for searching through a string haystack
/// in reverse (from the end) for occurrences of a pattern.
pub trait ReverseSearcher<'a, E: Encoding>: Searcher<'a, E> {
    /// Performs the next search step starting from the back.
    fn next_back(&mut self) -> SearchStep;

    /// Finds the next `Match` result from the back and returns the start and end indices.
    #[inline]
    fn next_match_back(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next_back() {
                SearchStep::Match(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                SearchStep::Reject(_, _) => continue,
            }
        }
    }

    /// Finds the next `Reject` result from the back and returns the start and end indices.
    #[inline]
    fn next_reject_back(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next_back() {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                SearchStep::Match(_, _) => continue,
            }
        }
    }
}

/// A marker trait for searchers that can be searched from both ends.
///
/// A `DoubleEndedSearcher` guarantees that searching from the front and
/// searching from the back will give the same sequence of matches, just
/// in reverse order.
pub trait DoubleEndedSearcher<'a, E: Encoding>: ReverseSearcher<'a, E> {}

/// A pattern that can be used to search within a string.
///
/// A `Pattern` expresses that the implementing type can be used as a string
/// pattern for searching in a `Str<E>`.
pub trait Pattern<'a, E: Encoding>: Sized {
    /// Associated searcher for this pattern.
    type Searcher: Searcher<'a, E>;

    /// Constructs the associated searcher from `self` and the `haystack` to search in.
    fn into_searcher(self, haystack: &'a Str<E>) -> Self::Searcher;

    /// Checks whether the pattern matches anywhere in the haystack.
    #[inline]
    fn is_contained_in(self, haystack: &'a Str<E>) -> bool {
        self.into_searcher(haystack).next_match().is_some()
    }

    /// Checks whether the pattern matches at the front of the haystack.
    #[inline]
    fn is_prefix_of(self, haystack: &'a Str<E>) -> bool {
        matches!(self.into_searcher(haystack).next(), SearchStep::Match(0, _))
    }

    /// Checks whether the pattern matches at the back of the haystack.
    #[inline]
    fn is_suffix_of(self, haystack: &'a Str<E>) -> bool
    where
        Self::Searcher: ReverseSearcher<'a, E>,
    {
        let len = haystack.len();
        matches!(
            self.into_searcher(haystack).next_back(),
            SearchStep::Match(_, b) if b == len
        )
    }

    /// Removes the pattern from the front of haystack, if it matches.
    #[inline]
    fn strip_prefix_of(self, haystack: &'a Str<E>) -> Option<&'a Str<E>> {
        if let SearchStep::Match(0, end) = self.into_searcher(haystack).next() {
            // SAFETY: We're splitting at a valid boundary
            Some(unsafe { Str::from_bytes_unchecked(&haystack.as_bytes()[end..]) })
        } else {
            None
        }
    }

    /// Removes the pattern from the back of haystack, if it matches.
    #[inline]
    fn strip_suffix_of(self, haystack: &'a Str<E>) -> Option<&'a Str<E>>
    where
        Self::Searcher: ReverseSearcher<'a, E>,
    {
        let len = haystack.len();
        if let SearchStep::Match(start, b) = self.into_searcher(haystack).next_back() {
            if b == len {
                // SAFETY: We're splitting at a valid boundary
                return Some(unsafe { Str::from_bytes_unchecked(&haystack.as_bytes()[..start]) });
            }
        }
        None
    }
}

// === Character searcher ===

/// Searcher for a `char` pattern.
pub struct CharSearcher<'a, E: Encoding> {
    haystack: &'a Str<E>,
    offset: usize,
    back_offset: usize,
    needle: char,
}

impl<'a, E: Encoding> CharSearcher<'a, E> {
    fn new(haystack: &'a Str<E>, needle: char) -> Self {
        Self {
            haystack,
            offset: 0,
            back_offset: haystack.len(),
            needle,
        }
    }
}

impl<'a, E: Encoding> Searcher<'a, E> for CharSearcher<'a, E> {
    fn haystack(&self) -> &'a Str<E> {
        self.haystack
    }

    fn remainder(&self) -> &'a Str<E> {
        unsafe {
            Str::from_bytes_unchecked(&self.haystack.as_bytes()[self.offset..self.back_offset])
        }
    }

    fn consumed(&self) -> usize {
        self.offset
    }

    fn next(&mut self) -> SearchStep {
        if self.offset >= self.back_offset {
            return SearchStep::Done;
        }

        let bytes = self.haystack.as_bytes();
        if let Some((c, next_offset)) = E::decode_char_at(bytes, self.offset) {
            let start = self.offset;
            self.offset = next_offset;
            if c == self.needle {
                SearchStep::Match(start, next_offset)
            } else {
                SearchStep::Reject(start, next_offset)
            }
        } else {
            SearchStep::Done
        }
    }
}

impl<'a, E: Encoding> ReverseSearcher<'a, E> for CharSearcher<'a, E> {
    fn next_back(&mut self) -> SearchStep {
        if self.offset >= self.back_offset {
            return SearchStep::Done;
        }

        let bytes = &self.haystack.as_bytes()[..self.back_offset];
        if let Some((c, start)) = E::decode_char_before(bytes, self.back_offset) {
            let end = self.back_offset;
            self.back_offset = start;
            if c == self.needle {
                SearchStep::Match(start, end)
            } else {
                SearchStep::Reject(start, end)
            }
        } else {
            SearchStep::Done
        }
    }
}

impl<'a, E: Encoding> DoubleEndedSearcher<'a, E> for CharSearcher<'a, E> {}

impl<'a, E: Encoding> Pattern<'a, E> for char {
    type Searcher = CharSearcher<'a, E>;

    fn into_searcher(self, haystack: &'a Str<E>) -> Self::Searcher {
        CharSearcher::new(haystack, self)
    }

    fn is_contained_in(self, haystack: &'a Str<E>) -> bool {
        haystack.chars().any(|c| c == self)
    }

    fn is_prefix_of(self, haystack: &'a Str<E>) -> bool {
        haystack.chars().next() == Some(self)
    }

    fn is_suffix_of(self, haystack: &'a Str<E>) -> bool
    where
        Self::Searcher: ReverseSearcher<'a, E>,
    {
        haystack.chars().next_back() == Some(self)
    }
}

// === Predicate searcher (FnMut(char) -> bool) ===

/// Searcher for a predicate pattern.
pub struct CharPredicateSearcher<'a, E: Encoding, F> {
    haystack: &'a Str<E>,
    offset: usize,
    back_offset: usize,
    predicate: F,
}

impl<'a, E: Encoding, F: FnMut(char) -> bool> CharPredicateSearcher<'a, E, F> {
    fn new(haystack: &'a Str<E>, predicate: F) -> Self {
        Self {
            haystack,
            offset: 0,
            back_offset: haystack.len(),
            predicate,
        }
    }
}

impl<'a, E: Encoding, F: FnMut(char) -> bool> Searcher<'a, E> for CharPredicateSearcher<'a, E, F> {
    fn haystack(&self) -> &'a Str<E> {
        self.haystack
    }

    fn remainder(&self) -> &'a Str<E> {
        unsafe {
            Str::from_bytes_unchecked(&self.haystack.as_bytes()[self.offset..self.back_offset])
        }
    }

    fn consumed(&self) -> usize {
        self.offset
    }

    fn next(&mut self) -> SearchStep {
        if self.offset >= self.back_offset {
            return SearchStep::Done;
        }

        let bytes = self.haystack.as_bytes();
        if let Some((c, next_offset)) = E::decode_char_at(bytes, self.offset) {
            let start = self.offset;
            self.offset = next_offset;
            if (self.predicate)(c) {
                SearchStep::Match(start, next_offset)
            } else {
                SearchStep::Reject(start, next_offset)
            }
        } else {
            SearchStep::Done
        }
    }
}

impl<'a, E: Encoding, F: FnMut(char) -> bool> ReverseSearcher<'a, E>
    for CharPredicateSearcher<'a, E, F>
{
    fn next_back(&mut self) -> SearchStep {
        if self.offset >= self.back_offset {
            return SearchStep::Done;
        }

        let bytes = &self.haystack.as_bytes()[..self.back_offset];
        if let Some((c, start)) = E::decode_char_before(bytes, self.back_offset) {
            let end = self.back_offset;
            self.back_offset = start;
            if (self.predicate)(c) {
                SearchStep::Match(start, end)
            } else {
                SearchStep::Reject(start, end)
            }
        } else {
            SearchStep::Done
        }
    }
}

impl<'a, E: Encoding, F: FnMut(char) -> bool> DoubleEndedSearcher<'a, E>
    for CharPredicateSearcher<'a, E, F>
{
}

impl<'a, E: Encoding, F: FnMut(char) -> bool> Pattern<'a, E> for F {
    type Searcher = CharPredicateSearcher<'a, E, F>;

    fn into_searcher(self, haystack: &'a Str<E>) -> Self::Searcher {
        CharPredicateSearcher::new(haystack, self)
    }
}

// === Character slice searcher (&[char]) ===

/// Searcher for a `&[char]` pattern.
pub struct CharSliceSearcher<'a, 'b, E: Encoding> {
    haystack: &'a Str<E>,
    offset: usize,
    back_offset: usize,
    chars: &'b [char],
}

impl<'a, 'b, E: Encoding> CharSliceSearcher<'a, 'b, E> {
    fn new(haystack: &'a Str<E>, chars: &'b [char]) -> Self {
        Self {
            haystack,
            offset: 0,
            back_offset: haystack.len(),
            chars,
        }
    }
}

impl<'a, 'b, E: Encoding> Searcher<'a, E> for CharSliceSearcher<'a, 'b, E> {
    fn haystack(&self) -> &'a Str<E> {
        self.haystack
    }

    fn remainder(&self) -> &'a Str<E> {
        unsafe {
            Str::from_bytes_unchecked(&self.haystack.as_bytes()[self.offset..self.back_offset])
        }
    }

    fn consumed(&self) -> usize {
        self.offset
    }

    fn next(&mut self) -> SearchStep {
        if self.offset >= self.back_offset {
            return SearchStep::Done;
        }

        let bytes = self.haystack.as_bytes();
        if let Some((c, next_offset)) = E::decode_char_at(bytes, self.offset) {
            let start = self.offset;
            self.offset = next_offset;
            if self.chars.contains(&c) {
                SearchStep::Match(start, next_offset)
            } else {
                SearchStep::Reject(start, next_offset)
            }
        } else {
            SearchStep::Done
        }
    }
}

impl<'a, 'b, E: Encoding> ReverseSearcher<'a, E> for CharSliceSearcher<'a, 'b, E> {
    fn next_back(&mut self) -> SearchStep {
        if self.offset >= self.back_offset {
            return SearchStep::Done;
        }

        let bytes = &self.haystack.as_bytes()[..self.back_offset];
        if let Some((c, start)) = E::decode_char_before(bytes, self.back_offset) {
            let end = self.back_offset;
            self.back_offset = start;
            if self.chars.contains(&c) {
                SearchStep::Match(start, end)
            } else {
                SearchStep::Reject(start, end)
            }
        } else {
            SearchStep::Done
        }
    }
}

impl<'a, 'b, E: Encoding> DoubleEndedSearcher<'a, E> for CharSliceSearcher<'a, 'b, E> {}

// === Character array searcher ([char; N]) ===

/// Searcher for a `[char; N]` pattern (owned array).
pub struct CharArraySearcher<'a, E: Encoding, const N: usize> {
    haystack: &'a Str<E>,
    offset: usize,
    back_offset: usize,
    chars: [char; N],
}

impl<'a, E: Encoding, const N: usize> CharArraySearcher<'a, E, N> {
    fn new(haystack: &'a Str<E>, chars: [char; N]) -> Self {
        Self {
            haystack,
            offset: 0,
            back_offset: haystack.len(),
            chars,
        }
    }
}

impl<'a, E: Encoding, const N: usize> Searcher<'a, E> for CharArraySearcher<'a, E, N> {
    fn haystack(&self) -> &'a Str<E> {
        self.haystack
    }

    fn remainder(&self) -> &'a Str<E> {
        unsafe {
            Str::from_bytes_unchecked(&self.haystack.as_bytes()[self.offset..self.back_offset])
        }
    }

    fn consumed(&self) -> usize {
        self.offset
    }

    fn next(&mut self) -> SearchStep {
        if self.offset >= self.back_offset {
            return SearchStep::Done;
        }

        let bytes = self.haystack.as_bytes();
        if let Some((c, next_offset)) = E::decode_char_at(bytes, self.offset) {
            let start = self.offset;
            self.offset = next_offset;
            if self.chars.contains(&c) {
                SearchStep::Match(start, next_offset)
            } else {
                SearchStep::Reject(start, next_offset)
            }
        } else {
            SearchStep::Done
        }
    }
}

impl<'a, E: Encoding, const N: usize> ReverseSearcher<'a, E> for CharArraySearcher<'a, E, N> {
    fn next_back(&mut self) -> SearchStep {
        if self.back_offset <= self.offset {
            return SearchStep::Done;
        }

        let bytes = &self.haystack.as_bytes()[..self.back_offset];
        if let Some((c, start)) = E::decode_char_before(bytes, self.back_offset) {
            let end = self.back_offset;
            self.back_offset = start;
            if self.chars.contains(&c) {
                SearchStep::Match(start, end)
            } else {
                SearchStep::Reject(start, end)
            }
        } else {
            SearchStep::Done
        }
    }
}

impl<'a, E: Encoding, const N: usize> DoubleEndedSearcher<'a, E> for CharArraySearcher<'a, E, N> {}

impl<'a, E: Encoding, const N: usize> Pattern<'a, E> for [char; N] {
    type Searcher = CharArraySearcher<'a, E, N>;

    fn into_searcher(self, haystack: &'a Str<E>) -> Self::Searcher {
        CharArraySearcher::new(haystack, self)
    }

    fn is_contained_in(self, haystack: &'a Str<E>) -> bool {
        if N == 0 {
            return false;
        }
        haystack.chars().any(|c| self.contains(&c))
    }

    fn is_prefix_of(self, haystack: &'a Str<E>) -> bool {
        if N == 0 {
            return false;
        }
        haystack.chars().next().map_or(false, |c| self.contains(&c))
    }

    fn is_suffix_of(self, haystack: &'a Str<E>) -> bool
    where
        Self::Searcher: ReverseSearcher<'a, E>,
    {
        if N == 0 {
            return false;
        }
        haystack
            .chars()
            .next_back()
            .map_or(false, |c| self.contains(&c))
    }
}

impl<'a, 'b, E: Encoding> Pattern<'a, E> for &'b [char] {
    type Searcher = CharSliceSearcher<'a, 'b, E>;

    fn into_searcher(self, haystack: &'a Str<E>) -> Self::Searcher {
        CharSliceSearcher::new(haystack, self)
    }

    fn is_contained_in(self, haystack: &'a Str<E>) -> bool {
        if self.is_empty() {
            return false;
        }
        haystack.chars().any(|c| self.contains(&c))
    }

    fn is_prefix_of(self, haystack: &'a Str<E>) -> bool {
        if self.is_empty() {
            return false;
        }
        haystack.chars().next().map_or(false, |c| self.contains(&c))
    }

    fn is_suffix_of(self, haystack: &'a Str<E>) -> bool
    where
        Self::Searcher: ReverseSearcher<'a, E>,
    {
        if self.is_empty() {
            return false;
        }
        haystack
            .chars()
            .next_back()
            .map_or(false, |c| self.contains(&c))
    }
}

impl<'a, 'b, E: Encoding, const N: usize> Pattern<'a, E> for &'b [char; N] {
    type Searcher = CharSliceSearcher<'a, 'b, E>;

    fn into_searcher(self, haystack: &'a Str<E>) -> Self::Searcher {
        CharSliceSearcher::new(haystack, self.as_slice())
    }

    fn is_contained_in(self, haystack: &'a Str<E>) -> bool {
        self.as_slice().is_contained_in(haystack)
    }

    fn is_prefix_of(self, haystack: &'a Str<E>) -> bool {
        self.as_slice().is_prefix_of(haystack)
    }

    fn is_suffix_of(self, haystack: &'a Str<E>) -> bool
    where
        Self::Searcher: ReverseSearcher<'a, E>,
    {
        self.as_slice().is_suffix_of(haystack)
    }
}

// === String pattern searcher (&Str<E>) ===

/// Searcher for a `&Str<E>` pattern.
pub struct StrSearcher<'a, 'b, E: Encoding> {
    haystack: &'a Str<E>,
    needle: &'b Str<E>,
    offset: usize,
    back_offset: usize,
    /// Flag to track completion of empty needle backward search
    empty_needle_done_back: bool,
}

impl<'a, 'b, E: Encoding> StrSearcher<'a, 'b, E> {
    fn new(haystack: &'a Str<E>, needle: &'b Str<E>) -> Self {
        Self {
            haystack,
            needle,
            offset: 0,
            back_offset: haystack.len(),
            empty_needle_done_back: false,
        }
    }
}

impl<'a, 'b, E: Encoding> Searcher<'a, E> for StrSearcher<'a, 'b, E> {
    fn haystack(&self) -> &'a Str<E> {
        self.haystack
    }

    fn remainder(&self) -> &'a Str<E> {
        unsafe {
            Str::from_bytes_unchecked(&self.haystack.as_bytes()[self.offset..self.back_offset])
        }
    }

    fn consumed(&self) -> usize {
        self.offset
    }

    fn next(&mut self) -> SearchStep {
        if self.offset > self.back_offset {
            return SearchStep::Done;
        }

        let needle_len = self.needle.len();

        // Empty needle matches at every position
        if needle_len == 0 {
            if self.offset <= self.back_offset {
                let pos = self.offset;
                // Move to next char boundary or end
                let bytes = self.haystack.as_bytes();
                if self.offset < self.haystack.len() {
                    if let Some((_, next)) = E::decode_char_at(bytes, self.offset) {
                        self.offset = next;
                    } else {
                        self.offset = self.back_offset + 1;
                    }
                } else {
                    self.offset = self.back_offset + 1;
                }
                return SearchStep::Match(pos, pos);
            }
            return SearchStep::Done;
        }

        let haystack_bytes = self.haystack.as_bytes();
        let needle_bytes = self.needle.as_bytes();

        // Search for needle starting from offset
        while self.offset + needle_len <= self.back_offset {
            if &haystack_bytes[self.offset..self.offset + needle_len] == needle_bytes {
                let start = self.offset;
                self.offset += needle_len;
                return SearchStep::Match(start, start + needle_len);
            }

            // Move to next char boundary
            if let Some((_, next)) = E::decode_char_at(haystack_bytes, self.offset) {
                let reject_start = self.offset;
                self.offset = next;
                return SearchStep::Reject(reject_start, next);
            } else {
                return SearchStep::Done;
            }
        }

        // Handle remaining bytes that can't contain the needle
        if self.offset < self.back_offset {
            let start = self.offset;
            self.offset = self.back_offset;
            return SearchStep::Reject(start, self.back_offset);
        }

        SearchStep::Done
    }
}

impl<'a, 'b, E: Encoding> ReverseSearcher<'a, E> for StrSearcher<'a, 'b, E> {
    fn next_back(&mut self) -> SearchStep {
        if self.offset > self.back_offset {
            return SearchStep::Done;
        }

        let needle_len = self.needle.len();

        // Empty needle matches at every position
        if needle_len == 0 {
            // Already completed empty needle backward search
            if self.empty_needle_done_back {
                return SearchStep::Done;
            }

            if self.back_offset > self.offset {
                let pos = self.back_offset;
                // Move to previous char boundary
                let bytes = &self.haystack.as_bytes()[..self.back_offset];
                if let Some((_, prev)) = E::decode_char_before(bytes, self.back_offset) {
                    self.back_offset = prev;
                } else {
                    self.back_offset = self.offset;
                }
                return SearchStep::Match(pos, pos);
            } else if self.back_offset == self.offset {
                // Final match at position offset (usually 0)
                self.empty_needle_done_back = true;
                return SearchStep::Match(self.offset, self.offset);
            }
            return SearchStep::Done;
        }

        let haystack_bytes = self.haystack.as_bytes();
        let needle_bytes = self.needle.as_bytes();

        // Search backwards for needle
        while self.back_offset >= self.offset + needle_len {
            let check_pos = self.back_offset - needle_len;
            if &haystack_bytes[check_pos..self.back_offset] == needle_bytes {
                // Verify it's on a char boundary
                if self.haystack.is_char_boundary(check_pos) {
                    let end = self.back_offset;
                    self.back_offset = check_pos;
                    return SearchStep::Match(check_pos, end);
                }
            }

            // Move to previous char boundary
            let bytes = &haystack_bytes[..self.back_offset];
            if let Some((_, prev)) = E::decode_char_before(bytes, self.back_offset) {
                let reject_end = self.back_offset;
                self.back_offset = prev;
                return SearchStep::Reject(prev, reject_end);
            } else {
                return SearchStep::Done;
            }
        }

        // Handle remaining bytes
        if self.back_offset > self.offset {
            let end = self.back_offset;
            self.back_offset = self.offset;
            return SearchStep::Reject(self.offset, end);
        }

        SearchStep::Done
    }
}

impl<'a, 'b, E: Encoding> Pattern<'a, E> for &'b Str<E> {
    type Searcher = StrSearcher<'a, 'b, E>;

    fn into_searcher(self, haystack: &'a Str<E>) -> Self::Searcher {
        StrSearcher::new(haystack, self)
    }

    fn is_contained_in(self, haystack: &'a Str<E>) -> bool {
        if self.is_empty() {
            return true;
        }
        // Simple byte search
        let needle = self.as_bytes();
        let hay = haystack.as_bytes();
        hay.windows(needle.len()).any(|w| w == needle)
    }

    fn is_prefix_of(self, haystack: &'a Str<E>) -> bool {
        haystack.as_bytes().starts_with(self.as_bytes())
    }

    fn is_suffix_of(self, haystack: &'a Str<E>) -> bool
    where
        Self::Searcher: ReverseSearcher<'a, E>,
    {
        haystack.as_bytes().ends_with(self.as_bytes())
    }
}

impl<'a, 'b, E: Encoding> Pattern<'a, E> for &'b crate::string::String<E> {
    type Searcher = StrSearcher<'a, 'b, E>;

    fn into_searcher(self, haystack: &'a Str<E>) -> Self::Searcher {
        let s: &Str<E> = self;
        StrSearcher::new(haystack, s)
    }

    fn is_contained_in(self, haystack: &'a Str<E>) -> bool {
        let s: &Str<E> = self;
        s.is_contained_in(haystack)
    }

    fn is_prefix_of(self, haystack: &'a Str<E>) -> bool {
        let s: &Str<E> = self;
        s.is_prefix_of(haystack)
    }

    fn is_suffix_of(self, haystack: &'a Str<E>) -> bool
    where
        Self::Searcher: ReverseSearcher<'a, E>,
    {
        let s: &Str<E> = self;
        s.is_suffix_of(haystack)
    }
}
