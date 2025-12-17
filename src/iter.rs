use core::fmt::Write;
use core::iter::FusedIterator;
use core::marker::PhantomData;

use crate::Str;
use crate::encoding::Encoding;
use crate::pattern::{ReverseSearcher, Searcher};

/// An iterator over the `char`s of a string slice.
pub struct Chars<'a, E: Encoding> {
    bytes: &'a [u8],
    offset: usize,
    _marker: PhantomData<E>,
}

impl<E: Encoding> Clone for Chars<'_, E> {
    fn clone(&self) -> Self {
        Self {
            bytes: self.bytes,
            offset: self.offset,
            _marker: PhantomData,
        }
    }
}

impl<'a, E: Encoding> Chars<'a, E> {
    #[inline]
    pub(crate) fn new(s: &'a Str<E>) -> Self {
        Self {
            bytes: s.as_bytes(),
            offset: 0,
            _marker: PhantomData,
        }
    }

    /// Views the underlying data as a subslice of the original data.
    #[inline]
    pub fn as_str(&self) -> &'a Str<E> {
        // SAFETY: We only advance offset to valid char boundaries
        unsafe { Str::from_bytes_unchecked(&self.bytes[self.offset..]) }
    }
}

impl<E: Encoding> Iterator for Chars<'_, E> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        if self.offset >= self.bytes.len() {
            return None;
        }
        let (c, next_offset) = E::decode_char_at(self.bytes, self.offset)?;
        self.offset = next_offset;
        Some(c)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.bytes.len() - self.offset;
        // At least 1 byte per char, at most MAX_CHAR_LEN bytes per char
        let min = remaining / E::MAX_CHAR_LEN;
        let max = remaining;
        (min.max(if remaining > 0 { 1 } else { 0 }), Some(max))
    }

    #[inline]
    fn count(self) -> usize {
        self.fold(0, |count, _| count + 1)
    }
}

impl<E: Encoding> DoubleEndedIterator for Chars<'_, E> {
    #[inline]
    fn next_back(&mut self) -> Option<char> {
        if self.offset >= self.bytes.len() {
            return None;
        }
        let (c, start) = E::decode_char_before(self.bytes, self.bytes.len())?;
        // For backwards iteration, we need to track where we've consumed up to.
        // This is tricky because we're iterating from both ends.
        // For simplicity, we'll rebuild the bytes slice.
        self.bytes = &self.bytes[..start];
        Some(c)
    }
}

impl<E: Encoding> FusedIterator for Chars<'_, E> {}

impl<E: Encoding> core::fmt::Debug for Chars<'_, E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Chars")
            .field("remaining", &self.as_str())
            .finish()
    }
}

/// An iterator over the `char`s of a string slice and their positions.
#[derive(Clone)]
pub struct CharIndices<'a, E: Encoding> {
    bytes: &'a [u8],
    offset: usize,
    front_offset: usize,
    _marker: PhantomData<E>,
}

impl<'a, E: Encoding> CharIndices<'a, E> {
    #[inline]
    pub(crate) fn new(s: &'a Str<E>) -> Self {
        Self {
            bytes: s.as_bytes(),
            offset: 0,
            front_offset: 0,
            _marker: PhantomData,
        }
    }

    /// Views the underlying data as a subslice of the original data.
    #[inline]
    pub fn as_str(&self) -> &'a Str<E> {
        // SAFETY: We only advance offset to valid char boundaries
        unsafe { Str::from_bytes_unchecked(&self.bytes[self.offset..]) }
    }

    /// Returns the byte position of the next character, or the length
    /// of the underlying string if there are no more characters.
    #[inline]
    pub fn offset(&self) -> usize {
        self.front_offset
    }
}

impl<E: Encoding> Iterator for CharIndices<'_, E> {
    type Item = (usize, char);

    #[inline]
    fn next(&mut self) -> Option<(usize, char)> {
        if self.offset >= self.bytes.len() {
            return None;
        }
        let (c, next_offset) = E::decode_char_at(self.bytes, self.offset)?;
        let char_start = self.offset;
        self.offset = next_offset;
        self.front_offset = self.offset;
        Some((char_start, c))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.bytes.len() - self.offset;
        let min = remaining / E::MAX_CHAR_LEN;
        let max = remaining;
        (min.max(if remaining > 0 { 1 } else { 0 }), Some(max))
    }

    #[inline]
    fn count(self) -> usize {
        self.fold(0, |count, _| count + 1)
    }
}

impl<E: Encoding> DoubleEndedIterator for CharIndices<'_, E> {
    #[inline]
    fn next_back(&mut self) -> Option<(usize, char)> {
        if self.offset >= self.bytes.len() {
            return None;
        }
        let (c, start) = E::decode_char_before(self.bytes, self.bytes.len())?;
        self.bytes = &self.bytes[..start];
        Some((start, c))
    }
}

impl<E: Encoding> FusedIterator for CharIndices<'_, E> {}

impl<E: Encoding> core::fmt::Debug for CharIndices<'_, E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("CharIndices")
            .field("remaining", &self.as_str())
            .finish()
    }
}

/// An iterator over the bytes of a string slice.
#[derive(Clone, Debug)]
pub struct Bytes<'a> {
    inner: core::slice::Iter<'a, u8>,
}

impl<'a> Bytes<'a> {
    #[inline]
    pub(crate) fn new(bytes: &'a [u8]) -> Self {
        Self {
            inner: bytes.iter(),
        }
    }
}

impl Iterator for Bytes<'_> {
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<u8> {
        self.inner.next().copied()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    #[inline]
    fn count(self) -> usize {
        self.inner.count()
    }

    #[inline]
    fn last(self) -> Option<u8> {
        self.inner.last().copied()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<u8> {
        self.inner.nth(n).copied()
    }
}

impl DoubleEndedIterator for Bytes<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<u8> {
        self.inner.next_back().copied()
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<u8> {
        self.inner.nth_back(n).copied()
    }
}

impl ExactSizeIterator for Bytes<'_> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl FusedIterator for Bytes<'_> {}

/// An iterator over the lines of a string, as string slices.
#[derive(Clone)]
pub struct Lines<'a, E: Encoding> {
    bytes: &'a [u8],
    offset: usize,
    back_offset: usize,
    _marker: PhantomData<E>,
}

impl<'a, E: Encoding> Lines<'a, E> {
    #[inline]
    pub(crate) fn new(s: &'a Str<E>) -> Self {
        Self {
            bytes: s.as_bytes(),
            offset: 0,
            back_offset: s.len(),
            _marker: PhantomData,
        }
    }
}

impl<'a, E: Encoding> Iterator for Lines<'a, E> {
    type Item = &'a Str<E>;

    fn next(&mut self) -> Option<&'a Str<E>> {
        if self.offset >= self.back_offset {
            return None;
        }

        let start = self.offset;
        let mut end = self.offset;

        // Find end of line
        while end < self.back_offset {
            if let Some((c, next)) = E::decode_char_at(self.bytes, end) {
                if c == '\n' {
                    let line_end = end;
                    self.offset = next;

                    // Strip trailing \r if present
                    let actual_end = if line_end > start {
                        if let Some((prev_c, _)) = E::decode_char_before(self.bytes, line_end) {
                            if prev_c == '\r' {
                                E::decode_char_before(self.bytes, line_end)
                                    .map(|(_, s)| s)
                                    .unwrap_or(line_end)
                            } else {
                                line_end
                            }
                        } else {
                            line_end
                        }
                    } else {
                        line_end
                    };

                    return Some(unsafe {
                        Str::from_bytes_unchecked(&self.bytes[start..actual_end])
                    });
                }
                end = next;
            } else {
                break;
            }
        }

        // Last line (no trailing newline)
        self.offset = self.back_offset;
        if start < self.back_offset {
            // Strip trailing \r if present
            let actual_end = if end > start {
                if let Some((prev_c, s)) = E::decode_char_before(self.bytes, end) {
                    if prev_c == '\r' { s } else { end }
                } else {
                    end
                }
            } else {
                end
            };
            Some(unsafe { Str::from_bytes_unchecked(&self.bytes[start..actual_end]) })
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.back_offset.saturating_sub(self.offset);
        (if remaining > 0 { 1 } else { 0 }, Some(remaining))
    }
}

impl<'a, E: Encoding> DoubleEndedIterator for Lines<'a, E> {
    fn next_back(&mut self) -> Option<&'a Str<E>> {
        if self.back_offset <= self.offset {
            return None;
        }

        // Skip trailing newline at back if present
        let mut end = self.back_offset;
        if end > self.offset {
            if let Some((c, start)) = E::decode_char_before(self.bytes, end) {
                if c == '\n' {
                    end = start;
                    // Also skip \r if it precedes the \n
                    if end > self.offset {
                        if let Some((c2, start2)) = E::decode_char_before(self.bytes, end) {
                            if c2 == '\r' {
                                end = start2;
                            }
                        }
                    }
                } else if c == '\r' {
                    end = start;
                }
            }
        }

        // Find start of this line (search backwards for newline)
        let line_end = end;
        let mut line_start = self.offset;
        let mut pos = end;
        while pos > self.offset {
            if let Some((c, start)) = E::decode_char_before(self.bytes, pos) {
                if c == '\n' {
                    line_start = pos;
                    break;
                }
                pos = start;
            } else {
                break;
            }
        }

        self.back_offset = line_start;

        // Strip trailing \r from line_end if present
        let actual_end = if line_end > line_start {
            if let Some((c, s)) = E::decode_char_before(self.bytes, line_end) {
                if c == '\r' { s } else { line_end }
            } else {
                line_end
            }
        } else {
            line_end
        };

        if line_start < actual_end || line_start == actual_end {
            Some(unsafe { Str::from_bytes_unchecked(&self.bytes[line_start..actual_end]) })
        } else {
            None
        }
    }
}

impl<E: Encoding> FusedIterator for Lines<'_, E> {}

impl<E: Encoding> core::fmt::Debug for Lines<'_, E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Lines").finish_non_exhaustive()
    }
}

/// An iterator over the non-whitespace substrings of a string.
#[derive(Clone)]
pub struct SplitWhitespace<'a, E: Encoding> {
    bytes: &'a [u8],
    offset: usize,
    back_offset: usize,
    _marker: PhantomData<E>,
}

impl<'a, E: Encoding> SplitWhitespace<'a, E> {
    #[inline]
    pub(crate) fn new(s: &'a Str<E>) -> Self {
        Self {
            bytes: s.as_bytes(),
            offset: 0,
            back_offset: s.len(),
            _marker: PhantomData,
        }
    }

    /// Returns remainder of the string being iterated.
    #[inline]
    pub fn remainder(&self) -> Option<&'a Str<E>> {
        if self.offset < self.back_offset {
            Some(unsafe { Str::from_bytes_unchecked(&self.bytes[self.offset..self.back_offset]) })
        } else {
            None
        }
    }
}

impl<'a, E: Encoding> Iterator for SplitWhitespace<'a, E> {
    type Item = &'a Str<E>;

    fn next(&mut self) -> Option<&'a Str<E>> {
        // Skip leading whitespace
        while self.offset < self.back_offset {
            if let Some((c, next)) = E::decode_char_at(self.bytes, self.offset) {
                if c.is_whitespace() {
                    self.offset = next;
                } else {
                    break;
                }
            } else {
                return None;
            }
        }

        if self.offset >= self.back_offset {
            return None;
        }

        // Find end of non-whitespace run
        let start = self.offset;
        while self.offset < self.back_offset {
            if let Some((c, next)) = E::decode_char_at(self.bytes, self.offset) {
                if c.is_whitespace() {
                    break;
                }
                self.offset = next;
            } else {
                break;
            }
        }

        Some(unsafe { Str::from_bytes_unchecked(&self.bytes[start..self.offset]) })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.back_offset.saturating_sub(self.offset);
        (0, Some(remaining))
    }
}

impl<'a, E: Encoding> DoubleEndedIterator for SplitWhitespace<'a, E> {
    fn next_back(&mut self) -> Option<&'a Str<E>> {
        // Skip trailing whitespace
        while self.back_offset > self.offset {
            if let Some((c, start)) = E::decode_char_before(self.bytes, self.back_offset) {
                if c.is_whitespace() {
                    self.back_offset = start;
                } else {
                    break;
                }
            } else {
                return None;
            }
        }

        if self.back_offset <= self.offset {
            return None;
        }

        // Find start of non-whitespace run
        let end = self.back_offset;
        while self.back_offset > self.offset {
            if let Some((c, start)) = E::decode_char_before(self.bytes, self.back_offset) {
                if c.is_whitespace() {
                    break;
                }
                self.back_offset = start;
            } else {
                break;
            }
        }

        Some(unsafe { Str::from_bytes_unchecked(&self.bytes[self.back_offset..end]) })
    }
}

impl<E: Encoding> FusedIterator for SplitWhitespace<'_, E> {}

impl<E: Encoding> core::fmt::Debug for SplitWhitespace<'_, E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SplitWhitespace").finish_non_exhaustive()
    }
}

/// An iterator over the non-ASCII-whitespace substrings of a string.
#[derive(Clone, Debug)]
pub struct SplitAsciiWhitespace<'a> {
    bytes: &'a [u8],
    offset: usize,
    back_offset: usize,
}

impl<'a> SplitAsciiWhitespace<'a> {
    #[inline]
    pub(crate) fn new(bytes: &'a [u8]) -> Self {
        Self {
            bytes,
            offset: 0,
            back_offset: bytes.len(),
        }
    }
}

impl<'a> Iterator for SplitAsciiWhitespace<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<&'a [u8]> {
        // Skip leading ASCII whitespace
        while self.offset < self.back_offset {
            if self.bytes[self.offset].is_ascii_whitespace() {
                self.offset += 1;
            } else {
                break;
            }
        }

        if self.offset >= self.back_offset {
            return None;
        }

        let start = self.offset;
        while self.offset < self.back_offset {
            if self.bytes[self.offset].is_ascii_whitespace() {
                break;
            }
            self.offset += 1;
        }

        Some(&self.bytes[start..self.offset])
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.back_offset.saturating_sub(self.offset)))
    }
}

impl<'a> DoubleEndedIterator for SplitAsciiWhitespace<'a> {
    fn next_back(&mut self) -> Option<&'a [u8]> {
        // Skip trailing ASCII whitespace
        while self.back_offset > self.offset {
            if self.bytes[self.back_offset - 1].is_ascii_whitespace() {
                self.back_offset -= 1;
            } else {
                break;
            }
        }

        if self.back_offset <= self.offset {
            return None;
        }

        let end = self.back_offset;
        while self.back_offset > self.offset {
            if self.bytes[self.back_offset - 1].is_ascii_whitespace() {
                break;
            }
            self.back_offset -= 1;
        }

        Some(&self.bytes[self.back_offset..end])
    }
}

impl FusedIterator for SplitAsciiWhitespace<'_> {}

/// Created with the method [`Str::split`].
pub struct Split<'a, E: Encoding, S: Searcher<'a, E>> {
    start: usize,
    searcher: S,
    finished: bool,
    _marker: PhantomData<&'a Str<E>>,
}

impl<'a, E: Encoding, S: Searcher<'a, E>> Split<'a, E, S> {
    #[inline]
    pub(crate) fn new(searcher: S) -> Self {
        Self {
            start: 0,
            searcher,
            finished: false,
            _marker: PhantomData,
        }
    }

    /// Returns the remainder of the string that hasn't been yielded yet.
    #[inline]
    pub(crate) fn remainder(&self) -> &'a Str<E> {
        unsafe { Str::from_bytes_unchecked(&self.searcher.haystack().as_bytes()[self.start..]) }
    }

    /// Marks the iterator as finished.
    #[inline]
    pub(crate) fn finish(&mut self) {
        self.finished = true;
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E>> Iterator for Split<'a, E, S> {
    type Item = &'a Str<E>;

    fn next(&mut self) -> Option<&'a Str<E>> {
        if self.finished {
            return None;
        }

        let haystack = self.searcher.haystack();

        match self.searcher.next_match() {
            Some((start, end)) => {
                // Return the part before the match
                let result =
                    unsafe { Str::from_bytes_unchecked(&haystack.as_bytes()[self.start..start]) };
                self.start = end;
                Some(result)
            }
            None => {
                // Return the remainder
                self.finished = true;
                Some(unsafe { Str::from_bytes_unchecked(&haystack.as_bytes()[self.start..]) })
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.finished {
            (0, Some(0))
        } else {
            let remaining = self.searcher.haystack().len() - self.start;
            (1, Some(remaining + 1))
        }
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E>> FusedIterator for Split<'a, E, S> {}

impl<'a, E: Encoding, S: Searcher<'a, E>> core::fmt::Debug for Split<'a, E, S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Split").finish_non_exhaustive()
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E> + Clone> Clone for Split<'a, E, S> {
    fn clone(&self) -> Self {
        Self {
            start: self.start,
            searcher: self.searcher.clone(),
            finished: self.finished,
            _marker: PhantomData,
        }
    }
}

/// Created with the method [`Str::split_inclusive`].
pub struct SplitInclusive<'a, E: Encoding, S: Searcher<'a, E>> {
    start: usize,
    searcher: S,
    finished: bool,
    _marker: PhantomData<&'a Str<E>>,
}

impl<'a, E: Encoding, S: Searcher<'a, E>> SplitInclusive<'a, E, S> {
    #[inline]
    pub(crate) fn new(searcher: S) -> Self {
        Self {
            start: 0,
            searcher,
            finished: false,
            _marker: PhantomData,
        }
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E>> Iterator for SplitInclusive<'a, E, S> {
    type Item = &'a Str<E>;

    fn next(&mut self) -> Option<&'a Str<E>> {
        if self.finished {
            return None;
        }

        let haystack = self.searcher.haystack();

        match self.searcher.next_match() {
            Some((_, end)) => {
                // Return the part including the match
                let result =
                    unsafe { Str::from_bytes_unchecked(&haystack.as_bytes()[self.start..end]) };
                self.start = end;
                Some(result)
            }
            None => {
                // Return the remainder if non-empty
                self.finished = true;
                if self.start < haystack.len() {
                    Some(unsafe { Str::from_bytes_unchecked(&haystack.as_bytes()[self.start..]) })
                } else {
                    None
                }
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.finished {
            (0, Some(0))
        } else {
            let remaining = self.searcher.haystack().len() - self.start;
            (1, Some(remaining + 1))
        }
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E>> FusedIterator for SplitInclusive<'a, E, S> {}

impl<'a, E: Encoding, S: Searcher<'a, E>> core::fmt::Debug for SplitInclusive<'a, E, S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SplitInclusive").finish_non_exhaustive()
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E> + Clone> Clone for SplitInclusive<'a, E, S> {
    fn clone(&self) -> Self {
        Self {
            start: self.start,
            searcher: self.searcher.clone(),
            finished: self.finished,
            _marker: PhantomData,
        }
    }
}

/// Created with the method [`Str::rsplit`].
pub struct RSplit<'a, E: Encoding, S: ReverseSearcher<'a, E>> {
    end: usize,
    searcher: S,
    finished: bool,
    _marker: PhantomData<&'a Str<E>>,
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> RSplit<'a, E, S> {
    #[inline]
    pub(crate) fn new(searcher: S) -> Self {
        let end = searcher.haystack().len();
        Self {
            end,
            searcher,
            finished: false,
            _marker: PhantomData,
        }
    }

    /// Returns the remainder of the string that hasn't been yielded yet.
    #[inline]
    pub(crate) fn remainder(&self) -> &'a Str<E> {
        unsafe { Str::from_bytes_unchecked(&self.searcher.haystack().as_bytes()[..self.end]) }
    }

    /// Marks the iterator as finished.
    #[inline]
    pub(crate) fn finish(&mut self) {
        self.finished = true;
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> Iterator for RSplit<'a, E, S> {
    type Item = &'a Str<E>;

    fn next(&mut self) -> Option<&'a Str<E>> {
        if self.finished {
            return None;
        }

        let haystack = self.searcher.haystack();

        match self.searcher.next_match_back() {
            Some((start, end)) => {
                // Return the part after the match
                let result =
                    unsafe { Str::from_bytes_unchecked(&haystack.as_bytes()[end..self.end]) };
                self.end = start;
                Some(result)
            }
            None => {
                // Return the remainder
                self.finished = true;
                Some(unsafe { Str::from_bytes_unchecked(&haystack.as_bytes()[..self.end]) })
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.finished {
            (0, Some(0))
        } else {
            (1, Some(self.end + 1))
        }
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> FusedIterator for RSplit<'a, E, S> {}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> core::fmt::Debug for RSplit<'a, E, S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("RSplit").finish_non_exhaustive()
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E> + Clone> Clone for RSplit<'a, E, S> {
    fn clone(&self) -> Self {
        Self {
            end: self.end,
            searcher: self.searcher.clone(),
            finished: self.finished,
            _marker: PhantomData,
        }
    }
}

/// Created with the method [`Str::split_terminator`].
///
/// Unlike [`Split`], this iterator does not yield an empty string at the end
/// if the string ends with the delimiter.
pub struct SplitTerminator<'a, E: Encoding, S: Searcher<'a, E>> {
    start: usize,
    searcher: S,
    finished: bool,
    _marker: PhantomData<&'a Str<E>>,
}

impl<'a, E: Encoding, S: Searcher<'a, E>> SplitTerminator<'a, E, S> {
    #[inline]
    pub(crate) fn new(searcher: S) -> Self {
        Self {
            start: 0,
            searcher,
            finished: false,
            _marker: PhantomData,
        }
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E>> Iterator for SplitTerminator<'a, E, S> {
    type Item = &'a Str<E>;

    fn next(&mut self) -> Option<&'a Str<E>> {
        if self.finished {
            return None;
        }

        let haystack = self.searcher.haystack();

        match self.searcher.next_match() {
            Some((start, end)) => {
                // Return the part before the match
                let result =
                    unsafe { Str::from_bytes_unchecked(&haystack.as_bytes()[self.start..start]) };
                self.start = end;
                Some(result)
            }
            None => {
                // Return the remainder only if non-empty
                self.finished = true;
                if self.start < haystack.len() {
                    Some(unsafe { Str::from_bytes_unchecked(&haystack.as_bytes()[self.start..]) })
                } else {
                    None
                }
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.finished {
            (0, Some(0))
        } else {
            let haystack = self.searcher.haystack();
            let remaining = haystack.len() - self.start;
            (if remaining > 0 { 1 } else { 0 }, Some(remaining + 1))
        }
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E>> FusedIterator for SplitTerminator<'a, E, S> {}

impl<'a, E: Encoding, S: Searcher<'a, E>> core::fmt::Debug for SplitTerminator<'a, E, S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SplitTerminator").finish_non_exhaustive()
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E> + Clone> Clone for SplitTerminator<'a, E, S> {
    fn clone(&self) -> Self {
        Self {
            start: self.start,
            searcher: self.searcher.clone(),
            finished: self.finished,
            _marker: PhantomData,
        }
    }
}

/// Created with the method [`Str::rsplit_terminator`].
///
/// Unlike [`RSplit`], this iterator does not yield an empty string at the start
/// if the string ends with the delimiter (since we're iterating in reverse).
pub struct RSplitTerminator<'a, E: Encoding, S: ReverseSearcher<'a, E>> {
    end: usize,
    searcher: S,
    finished: bool,
    first: bool,
    _marker: PhantomData<&'a Str<E>>,
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> RSplitTerminator<'a, E, S> {
    #[inline]
    pub(crate) fn new(searcher: S) -> Self {
        let end = searcher.haystack().len();
        Self {
            end,
            searcher,
            finished: false,
            first: true,
            _marker: PhantomData,
        }
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> Iterator for RSplitTerminator<'a, E, S> {
    type Item = &'a Str<E>;

    fn next(&mut self) -> Option<&'a Str<E>> {
        if self.finished {
            return None;
        }

        let haystack = self.searcher.haystack();

        // On first iteration, check if we match at end and skip if so
        if self.first {
            self.first = false;
            if let Some((start, end)) = self.searcher.next_match_back() {
                if end == self.end {
                    // Pattern matches at end, skip it (terminator behavior)
                    self.end = start;
                    // Now search for next match
                    return self.next_inner();
                } else {
                    // Match wasn't at end, return suffix
                    let result =
                        unsafe { Str::from_bytes_unchecked(&haystack.as_bytes()[end..self.end]) };
                    self.end = start;
                    return Some(result);
                }
            } else {
                // No matches at all, return everything if non-empty
                self.finished = true;
                if self.end > 0 {
                    return Some(unsafe {
                        Str::from_bytes_unchecked(&haystack.as_bytes()[..self.end])
                    });
                }
                return None;
            }
        }

        self.next_inner()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.finished {
            (0, Some(0))
        } else {
            (if self.end > 0 { 1 } else { 0 }, Some(self.end + 1))
        }
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> RSplitTerminator<'a, E, S> {
    fn next_inner(&mut self) -> Option<&'a Str<E>> {
        let haystack = self.searcher.haystack();

        match self.searcher.next_match_back() {
            Some((start, end)) => {
                // Return the part after the match
                let result =
                    unsafe { Str::from_bytes_unchecked(&haystack.as_bytes()[end..self.end]) };
                self.end = start;
                Some(result)
            }
            None => {
                // Return the remainder only if non-empty
                self.finished = true;
                if self.end > 0 {
                    Some(unsafe { Str::from_bytes_unchecked(&haystack.as_bytes()[..self.end]) })
                } else {
                    None
                }
            }
        }
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> FusedIterator for RSplitTerminator<'a, E, S> {}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> core::fmt::Debug for RSplitTerminator<'a, E, S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("RSplitTerminator").finish_non_exhaustive()
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E> + Clone> Clone for RSplitTerminator<'a, E, S> {
    fn clone(&self) -> Self {
        Self {
            end: self.end,
            searcher: self.searcher.clone(),
            finished: self.finished,
            first: self.first,
            _marker: PhantomData,
        }
    }
}

/// Created with the method [`Str::splitn`].
pub struct SplitN<'a, E: Encoding, S: Searcher<'a, E>> {
    inner: Split<'a, E, S>,
    count: usize,
}

impl<'a, E: Encoding, S: Searcher<'a, E>> SplitN<'a, E, S> {
    #[inline]
    pub(crate) fn new(searcher: S, n: usize) -> Self {
        Self {
            inner: Split::new(searcher),
            count: n,
        }
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E>> Iterator for SplitN<'a, E, S> {
    type Item = &'a Str<E>;

    fn next(&mut self) -> Option<&'a Str<E>> {
        if self.count == 0 {
            return None;
        }
        self.count -= 1;
        if self.count == 0 {
            // Return the rest
            let remainder = self.inner.remainder();
            self.inner.finish();
            Some(remainder)
        } else {
            self.inner.next()
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (lower, upper) = self.inner.size_hint();
        (lower.min(self.count), upper.map(|u| u.min(self.count)))
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E>> FusedIterator for SplitN<'a, E, S> {}

impl<'a, E: Encoding, S: Searcher<'a, E>> core::fmt::Debug for SplitN<'a, E, S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SplitN").finish_non_exhaustive()
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E> + Clone> Clone for SplitN<'a, E, S> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            count: self.count,
        }
    }
}

/// Created with the method [`Str::rsplitn`].
pub struct RSplitN<'a, E: Encoding, S: ReverseSearcher<'a, E>> {
    inner: RSplit<'a, E, S>,
    count: usize,
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> RSplitN<'a, E, S> {
    #[inline]
    pub(crate) fn new(searcher: S, n: usize) -> Self {
        Self {
            inner: RSplit::new(searcher),
            count: n,
        }
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> Iterator for RSplitN<'a, E, S> {
    type Item = &'a Str<E>;

    fn next(&mut self) -> Option<&'a Str<E>> {
        if self.count == 0 {
            return None;
        }
        self.count -= 1;
        if self.count == 0 {
            let remainder = self.inner.remainder();
            self.inner.finish();
            Some(remainder)
        } else {
            self.inner.next()
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (lower, upper) = self.inner.size_hint();
        (lower.min(self.count), upper.map(|u| u.min(self.count)))
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> FusedIterator for RSplitN<'a, E, S> {}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> core::fmt::Debug for RSplitN<'a, E, S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("RSplitN").finish_non_exhaustive()
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E> + Clone> Clone for RSplitN<'a, E, S> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            count: self.count,
        }
    }
}

/// Created with the method [`Str::matches`].
pub struct Matches<'a, E: Encoding, S: Searcher<'a, E>> {
    searcher: S,
    _marker: PhantomData<&'a Str<E>>,
}

impl<'a, E: Encoding, S: Searcher<'a, E>> Matches<'a, E, S> {
    #[inline]
    pub(crate) fn new(searcher: S) -> Self {
        Self {
            searcher,
            _marker: PhantomData,
        }
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E>> Iterator for Matches<'a, E, S> {
    type Item = &'a Str<E>;

    fn next(&mut self) -> Option<&'a Str<E>> {
        let haystack = self.searcher.haystack();
        self.searcher.next_match().map(|(start, end)| unsafe {
            Str::from_bytes_unchecked(&haystack.as_bytes()[start..end])
        })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.searcher.haystack().len()))
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E>> FusedIterator for Matches<'a, E, S> {}

impl<'a, E: Encoding, S: Searcher<'a, E>> core::fmt::Debug for Matches<'a, E, S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Matches").finish_non_exhaustive()
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E> + Clone> Clone for Matches<'a, E, S> {
    fn clone(&self) -> Self {
        Self {
            searcher: self.searcher.clone(),
            _marker: PhantomData,
        }
    }
}

/// Created with the method [`Str::rmatches`].
pub struct RMatches<'a, E: Encoding, S: ReverseSearcher<'a, E>> {
    searcher: S,
    _marker: PhantomData<&'a Str<E>>,
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> RMatches<'a, E, S> {
    #[inline]
    pub(crate) fn new(searcher: S) -> Self {
        Self {
            searcher,
            _marker: PhantomData,
        }
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> Iterator for RMatches<'a, E, S> {
    type Item = &'a Str<E>;

    fn next(&mut self) -> Option<&'a Str<E>> {
        let haystack = self.searcher.haystack();
        self.searcher.next_match_back().map(|(start, end)| unsafe {
            Str::from_bytes_unchecked(&haystack.as_bytes()[start..end])
        })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.searcher.haystack().len()))
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> FusedIterator for RMatches<'a, E, S> {}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> core::fmt::Debug for RMatches<'a, E, S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("RMatches").finish_non_exhaustive()
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E> + Clone> Clone for RMatches<'a, E, S> {
    fn clone(&self) -> Self {
        Self {
            searcher: self.searcher.clone(),
            _marker: PhantomData,
        }
    }
}

/// Created with the method [`Str::match_indices`].
pub struct MatchIndices<'a, E: Encoding, S: Searcher<'a, E>> {
    searcher: S,
    _marker: PhantomData<&'a Str<E>>,
}

impl<'a, E: Encoding, S: Searcher<'a, E>> MatchIndices<'a, E, S> {
    #[inline]
    pub(crate) fn new(searcher: S) -> Self {
        Self {
            searcher,
            _marker: PhantomData,
        }
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E>> Iterator for MatchIndices<'a, E, S> {
    type Item = (usize, &'a Str<E>);

    fn next(&mut self) -> Option<(usize, &'a Str<E>)> {
        let haystack = self.searcher.haystack();
        self.searcher.next_match().map(|(start, end)| {
            (start, unsafe {
                Str::from_bytes_unchecked(&haystack.as_bytes()[start..end])
            })
        })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.searcher.haystack().len()))
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E>> FusedIterator for MatchIndices<'a, E, S> {}

impl<'a, E: Encoding, S: Searcher<'a, E>> core::fmt::Debug for MatchIndices<'a, E, S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("MatchIndices").finish_non_exhaustive()
    }
}

impl<'a, E: Encoding, S: Searcher<'a, E> + Clone> Clone for MatchIndices<'a, E, S> {
    fn clone(&self) -> Self {
        Self {
            searcher: self.searcher.clone(),
            _marker: PhantomData,
        }
    }
}

/// Created with the method [`Str::rmatch_indices`].
pub struct RMatchIndices<'a, E: Encoding, S: ReverseSearcher<'a, E>> {
    searcher: S,
    _marker: PhantomData<&'a Str<E>>,
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> RMatchIndices<'a, E, S> {
    #[inline]
    pub(crate) fn new(searcher: S) -> Self {
        Self {
            searcher,
            _marker: PhantomData,
        }
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> Iterator for RMatchIndices<'a, E, S> {
    type Item = (usize, &'a Str<E>);

    fn next(&mut self) -> Option<(usize, &'a Str<E>)> {
        let haystack = self.searcher.haystack();
        self.searcher.next_match_back().map(|(start, end)| {
            (start, unsafe {
                Str::from_bytes_unchecked(&haystack.as_bytes()[start..end])
            })
        })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.searcher.haystack().len()))
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> FusedIterator for RMatchIndices<'a, E, S> {}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E>> core::fmt::Debug for RMatchIndices<'a, E, S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("RMatchIndices").finish_non_exhaustive()
    }
}

impl<'a, E: Encoding, S: ReverseSearcher<'a, E> + Clone> Clone for RMatchIndices<'a, E, S> {
    fn clone(&self) -> Self {
        Self {
            searcher: self.searcher.clone(),
            _marker: PhantomData,
        }
    }
}

/// A draining iterator for `String<E>`.
pub struct Drain<'a, E: Encoding> {
    /// Start of the drain range
    start: usize,
    /// End of the drain range
    end: usize,
    /// Iterator over the chars being drained
    iter: Chars<'a, E>,
    /// Pointer back to the string (for drop)
    string: *mut crate::String<E>,
}

impl<'a, E: Encoding> Drain<'a, E> {
    #[inline]
    pub(crate) fn new(string: &'a mut crate::String<E>, start: usize, end: usize) -> Self {
        // SAFETY: We have exclusive access to the string
        // Take the pointer first to avoid borrow conflicts
        let ptr = string as *mut crate::String<E>;
        let slice = unsafe {
            let bytes = (*ptr).as_bytes();
            Str::from_bytes_unchecked(&bytes[start..end])
        };
        Self {
            start,
            end,
            iter: Chars::new(slice),
            string: ptr,
        }
    }

    /// Returns the remaining (sub)string of this iterator as a slice.
    #[inline]
    pub fn as_str(&self) -> &Str<E> {
        self.iter.as_str()
    }
}

impl<E: Encoding> Iterator for Drain<'_, E> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        // Count remaining chars for accurate size_hint (matches std behavior)
        let count = self.iter.clone().count();
        (count, Some(count))
    }
}

impl<E: Encoding> DoubleEndedIterator for Drain<'_, E> {
    #[inline]
    fn next_back(&mut self) -> Option<char> {
        self.iter.next_back()
    }
}

impl<E: Encoding> FusedIterator for Drain<'_, E> {}

impl<E: Encoding> Drop for Drain<'_, E> {
    fn drop(&mut self) {
        // SAFETY: We have the only reference to the string
        unsafe {
            let string = &mut *self.string;
            let vec = string.as_mut_vec();
            // Remove the drained portion
            vec.drain(self.start..self.end);
        }
    }
}

impl<E: Encoding> core::fmt::Debug for Drain<'_, E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Drain")
            .field("remaining", &self.as_str())
            .finish()
    }
}

// SAFETY: Drain keeps a mutable reference to the string
unsafe impl<E: Encoding + Send> Send for Drain<'_, E> {}
unsafe impl<E: Encoding + Sync> Sync for Drain<'_, E> {}

/// An iterator that escapes each character in a string using [`char::escape_debug`].
pub struct EscapeDebug<'a, E: Encoding> {
    inner: core::iter::FlatMap<
        Chars<'a, E>,
        core::char::EscapeDebug,
        fn(char) -> core::char::EscapeDebug,
    >,
}

impl<'a, E: Encoding> EscapeDebug<'a, E> {
    #[inline]
    pub(crate) fn new(s: &'a Str<E>) -> Self {
        Self {
            inner: s
                .chars()
                .flat_map(char::escape_debug as fn(char) -> core::char::EscapeDebug),
        }
    }
}

impl<E: Encoding> Clone for EscapeDebug<'_, E> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<E: Encoding> Iterator for EscapeDebug<'_, E> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        self.inner.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<E: Encoding> FusedIterator for EscapeDebug<'_, E> {}

impl<E: Encoding> core::fmt::Debug for EscapeDebug<'_, E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("EscapeDebug").finish_non_exhaustive()
    }
}

impl<E: Encoding> core::fmt::Display for EscapeDebug<'_, E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut iter = self.clone();
        while let Some(c) = iter.next() {
            f.write_char(c)?;
        }
        Ok(())
    }
}

/// An iterator that escapes each character in a string using [`char::escape_default`].
pub struct EscapeDefault<'a, E: Encoding> {
    inner: core::iter::FlatMap<
        Chars<'a, E>,
        core::char::EscapeDefault,
        fn(char) -> core::char::EscapeDefault,
    >,
}

impl<'a, E: Encoding> EscapeDefault<'a, E> {
    #[inline]
    pub(crate) fn new(s: &'a Str<E>) -> Self {
        Self {
            inner: s
                .chars()
                .flat_map(char::escape_default as fn(char) -> core::char::EscapeDefault),
        }
    }
}

impl<E: Encoding> Clone for EscapeDefault<'_, E> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<E: Encoding> Iterator for EscapeDefault<'_, E> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        self.inner.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<E: Encoding> FusedIterator for EscapeDefault<'_, E> {}

impl<E: Encoding> core::fmt::Debug for EscapeDefault<'_, E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("EscapeDefault").finish_non_exhaustive()
    }
}

impl<E: Encoding> core::fmt::Display for EscapeDefault<'_, E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut iter = self.clone();
        while let Some(c) = iter.next() {
            f.write_char(c)?;
        }
        Ok(())
    }
}

/// An iterator that escapes each character in a string using [`char::escape_unicode`].
pub struct EscapeUnicode<'a, E: Encoding> {
    inner: core::iter::FlatMap<
        Chars<'a, E>,
        core::char::EscapeUnicode,
        fn(char) -> core::char::EscapeUnicode,
    >,
}

impl<'a, E: Encoding> EscapeUnicode<'a, E> {
    #[inline]
    pub(crate) fn new(s: &'a Str<E>) -> Self {
        Self {
            inner: s
                .chars()
                .flat_map(char::escape_unicode as fn(char) -> core::char::EscapeUnicode),
        }
    }
}

impl<E: Encoding> Clone for EscapeUnicode<'_, E> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<E: Encoding> Iterator for EscapeUnicode<'_, E> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        self.inner.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<E: Encoding> FusedIterator for EscapeUnicode<'_, E> {}

impl<E: Encoding> core::fmt::Debug for EscapeUnicode<'_, E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("EscapeUnicode").finish_non_exhaustive()
    }
}

impl<E: Encoding> core::fmt::Display for EscapeUnicode<'_, E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut iter = self.clone();
        while let Some(c) = iter.next() {
            f.write_char(c)?;
        }
        Ok(())
    }
}
