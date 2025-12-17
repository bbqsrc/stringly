use core::borrow::{Borrow, BorrowMut};
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::iter::FromIterator;
use core::marker::PhantomData;
use core::ops::{
    Add, AddAssign, Deref, DerefMut, Index, IndexMut, Range, RangeBounds, RangeFrom, RangeFull,
    RangeInclusive, RangeTo, RangeToInclusive,
};

use crate::Str;
use crate::encoding::Encoding;
use crate::error::FromBytesError;
use crate::iter::Drain;
use crate::pattern::{Pattern, Searcher};

/// An owned string in encoding `E`.
///
/// This is the owned counterpart to [`Str<E>`], analogous to how
/// `std::string::String` relates to `str`.
pub struct String<E: Encoding> {
    bytes: Vec<u8>,
    _marker: PhantomData<E>,
}

impl<E: Encoding> String<E> {
    // === Construction ===

    /// Creates a new empty `String`.
    #[inline]
    pub const fn new() -> Self {
        Self {
            bytes: Vec::new(),
            _marker: PhantomData,
        }
    }

    /// Creates a new empty `String` with at least the specified capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            bytes: Vec::with_capacity(capacity),
            _marker: PhantomData,
        }
    }

    /// Tries to create a new empty `String` with at least the specified capacity.
    ///
    /// Returns an error if the capacity cannot be allocated.
    #[inline]
    pub fn try_with_capacity(capacity: usize) -> Result<Self, std::collections::TryReserveError> {
        let mut bytes = Vec::new();
        bytes.try_reserve(capacity)?;
        Ok(Self {
            bytes,
            _marker: PhantomData,
        })
    }

    /// Converts a vector of bytes to a `String`.
    ///
    /// Returns an error if the bytes are not valid for this encoding.
    #[inline]
    pub fn from_bytes(bytes: Vec<u8>) -> Result<Self, FromBytesError<E>> {
        match E::validate(&bytes) {
            Ok(()) => Ok(Self {
                bytes,
                _marker: PhantomData,
            }),
            Err(e) => Err(FromBytesError::new(bytes, e)),
        }
    }

    /// Converts a vector of bytes to a `String` without checking validity.
    ///
    /// # Safety
    ///
    /// The bytes must be valid for this encoding.
    #[inline]
    pub unsafe fn from_bytes_unchecked(bytes: Vec<u8>) -> Self {
        Self {
            bytes,
            _marker: PhantomData,
        }
    }

    /// Converts a slice of bytes to a `String`, replacing invalid sequences
    /// with the Unicode replacement character (U+FFFD).
    ///
    /// # Examples
    ///
    /// ```
    /// use stringly::{String, Utf8};
    ///
    /// // Valid UTF-8
    /// let valid = b"hello";
    /// let s: String<Utf8> = String::from_bytes_lossy(valid);
    /// assert_eq!(s.chars().collect::<std::string::String>(), "hello");
    ///
    /// // Invalid UTF-8 (0xFF is not valid)
    /// let invalid = b"hello\xFFworld";
    /// let s: String<Utf8> = String::from_bytes_lossy(invalid);
    /// assert_eq!(s.chars().collect::<std::string::String>(), "hello\u{FFFD}world");
    /// ```
    pub fn from_bytes_lossy(bytes: &[u8]) -> Self {
        // Fast path: if already valid, just copy
        if E::validate(bytes).is_ok() {
            return Self {
                bytes: bytes.to_vec(),
                _marker: PhantomData,
            };
        }

        // Slow path: scan and replace invalid sequences
        let mut result = Self::with_capacity(bytes.len());
        let mut offset = 0;

        while offset < bytes.len() {
            // Try to decode a character at this position
            if let Some((c, next)) = E::decode_char_at(bytes, offset) {
                result.push(c);
                offset = next;
            } else {
                // Invalid byte sequence - emit replacement character and skip one byte
                result.push('\u{FFFD}');
                offset += 1;
            }
        }

        result
    }

    /// Decomposes a `String<E>` into its raw components.
    ///
    /// Returns the raw pointer to the underlying data, the length of
    /// the string (in bytes), and the allocated capacity of the data
    /// (in bytes).
    ///
    /// After calling this function, the caller is responsible for the
    /// memory previously managed by the `String`. The only way to do
    /// this is to convert the raw pointer, length, and capacity back
    /// into a `String` with the [`from_raw_parts`] function.
    ///
    /// [`from_raw_parts`]: Self::from_raw_parts
    ///
    /// # Examples
    ///
    /// ```
    /// use stringly::{String, Utf8};
    ///
    /// let s: String<Utf8> = "hello".chars().collect();
    /// let (ptr, len, cap) = s.into_raw_parts();
    ///
    /// // Reconstruct the String
    /// let s = unsafe { String::<Utf8>::from_raw_parts(ptr, len, cap) };
    /// ```
    #[inline]
    pub fn into_raw_parts(self) -> (*mut u8, usize, usize) {
        let mut me = core::mem::ManuallyDrop::new(self);
        (me.bytes.as_mut_ptr(), me.bytes.len(), me.bytes.capacity())
    }

    /// Creates a new `String<E>` from a pointer, a length, and a capacity.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked:
    ///
    /// * The memory at `buf` needs to have been previously allocated by the
    ///   same allocator the standard library uses, with a required alignment
    ///   of exactly 1.
    /// * `length` needs to be less than or equal to `capacity`.
    /// * `capacity` needs to be the correct value.
    /// * The first `length` bytes at `buf` need to be valid for encoding `E`.
    ///
    /// Violating these may cause problems like corrupting the allocator's
    /// internal data structures.
    ///
    /// # Examples
    ///
    /// ```
    /// use stringly::{String, Utf8};
    ///
    /// let s: String<Utf8> = "hello".chars().collect();
    /// let (ptr, len, cap) = s.into_raw_parts();
    ///
    /// // Reconstruct the String
    /// let s = unsafe { String::<Utf8>::from_raw_parts(ptr, len, cap) };
    /// assert_eq!(s.chars().collect::<std::string::String>(), "hello");
    /// ```
    #[inline]
    pub unsafe fn from_raw_parts(buf: *mut u8, length: usize, capacity: usize) -> Self {
        // SAFETY: caller guarantees the invariants
        unsafe {
            Self {
                bytes: Vec::from_raw_parts(buf, length, capacity),
                _marker: PhantomData,
            }
        }
    }

    // === Capacity ===

    /// Returns this `String`'s capacity, in bytes.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.bytes.capacity()
    }

    /// Reserves capacity for at least `additional` bytes more than the current length.
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.bytes.reserve(additional);
    }

    /// Reserves the minimum capacity for at least `additional` bytes more than the current length.
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.bytes.reserve_exact(additional);
    }

    /// Tries to reserve capacity for at least `additional` bytes more than the current length.
    #[inline]
    pub fn try_reserve(
        &mut self,
        additional: usize,
    ) -> Result<(), std::collections::TryReserveError> {
        self.bytes.try_reserve(additional)
    }

    /// Tries to reserve the minimum capacity for at least `additional` bytes more than the current length.
    #[inline]
    pub fn try_reserve_exact(
        &mut self,
        additional: usize,
    ) -> Result<(), std::collections::TryReserveError> {
        self.bytes.try_reserve_exact(additional)
    }

    /// Shrinks the capacity of this `String` to match its length.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.bytes.shrink_to_fit();
    }

    /// Shrinks the capacity of this `String` with a lower bound.
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.bytes.shrink_to(min_capacity);
    }

    // === Mutation ===

    /// Appends the given `char` to the end of this `String`.
    pub fn push(&mut self, ch: char) {
        let mut buf = [0u8; 4];
        let len = E::encode_char(ch, &mut buf);
        self.bytes.extend_from_slice(&buf[..len]);
    }

    /// Appends a given string slice onto the end of this `String`.
    #[inline]
    pub fn push_str(&mut self, string: &Str<E>) {
        self.bytes.extend_from_slice(string.as_bytes());
    }

    /// Copies elements from `src` range to the end of the string.
    pub fn extend_from_within<R: RangeBounds<usize>>(&mut self, src: R) {
        let start = match src.start_bound() {
            core::ops::Bound::Included(&n) => n,
            core::ops::Bound::Excluded(&n) => n + 1,
            core::ops::Bound::Unbounded => 0,
        };
        let end = match src.end_bound() {
            core::ops::Bound::Included(&n) => n + 1,
            core::ops::Bound::Excluded(&n) => n,
            core::ops::Bound::Unbounded => self.len(),
        };

        assert!(self.is_char_boundary(start), "start is not a char boundary");
        assert!(self.is_char_boundary(end), "end is not a char boundary");
        assert!(start <= end && end <= self.len(), "range out of bounds");

        self.bytes.extend_from_within(start..end);
    }

    /// Removes the last character from the string and returns it.
    pub fn pop(&mut self) -> Option<char> {
        if self.bytes.is_empty() {
            return None;
        }

        let (c, start) = E::decode_char_before(&self.bytes, self.bytes.len())?;
        self.bytes.truncate(start);
        Some(c)
    }

    /// Removes a `char` from this `String` at a byte position and returns it.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than or equal to the `String`'s length,
    /// or if it does not lie on a `char` boundary.
    pub fn remove(&mut self, idx: usize) -> char {
        assert!(self.is_char_boundary(idx), "idx is not a char boundary");
        let (c, end) = E::decode_char_at(&self.bytes, idx).expect("idx is out of bounds");
        self.bytes.drain(idx..end);
        c
    }

    /// Remove all matches of pattern `pat` in the `String`.
    pub fn remove_matches<P: for<'a> Pattern<'a, E>>(&mut self, pat: P) {
        // Collect match ranges first to avoid borrow issues
        let matches: Vec<(usize, usize)> = {
            let mut searcher = pat.into_searcher(self.as_str());
            let mut matches = Vec::new();
            while let Some(m) = searcher.next_match() {
                matches.push(m);
            }
            matches
        };

        if matches.is_empty() {
            return;
        }

        let mut result = Vec::with_capacity(self.len());
        let mut last_end = 0;

        for (start, end) in matches {
            result.extend_from_slice(&self.bytes[last_end..start]);
            last_end = end;
        }
        result.extend_from_slice(&self.bytes[last_end..]);

        self.bytes = result;
    }

    /// Inserts a character into this `String` at a byte position.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `String`'s length, or if it does
    /// not lie on a `char` boundary.
    pub fn insert(&mut self, idx: usize, ch: char) {
        assert!(self.is_char_boundary(idx), "idx is not a char boundary");
        let mut buf = [0u8; 4];
        let len = E::encode_char(ch, &mut buf);

        // Make room for the new bytes
        self.bytes.reserve(len);
        let old_len = self.bytes.len();
        unsafe {
            self.bytes.set_len(old_len + len);
            // Move existing bytes to make room
            core::ptr::copy(
                self.bytes.as_ptr().add(idx),
                self.bytes.as_mut_ptr().add(idx + len),
                old_len - idx,
            );
            // Copy in the new character
            core::ptr::copy_nonoverlapping(buf.as_ptr(), self.bytes.as_mut_ptr().add(idx), len);
        }
    }

    /// Inserts a string slice into this `String` at a byte position.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `String`'s length, or if it does
    /// not lie on a `char` boundary.
    pub fn insert_str(&mut self, idx: usize, string: &Str<E>) {
        assert!(self.is_char_boundary(idx), "idx is not a char boundary");
        let insert_bytes = string.as_bytes();
        let insert_len = insert_bytes.len();

        // Make room for the new bytes
        self.bytes.reserve(insert_len);
        let old_len = self.bytes.len();
        unsafe {
            self.bytes.set_len(old_len + insert_len);
            // Move existing bytes to make room
            core::ptr::copy(
                self.bytes.as_ptr().add(idx),
                self.bytes.as_mut_ptr().add(idx + insert_len),
                old_len - idx,
            );
            // Copy in the new string
            core::ptr::copy_nonoverlapping(
                insert_bytes.as_ptr(),
                self.bytes.as_mut_ptr().add(idx),
                insert_len,
            );
        }
    }

    /// Truncates this `String`, removing all contents.
    #[inline]
    pub fn clear(&mut self) {
        self.bytes.clear();
    }

    /// Shortens this `String` to the specified length.
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a `char` boundary.
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len < self.len() {
            assert!(
                self.is_char_boundary(new_len),
                "new_len is not a char boundary"
            );
            self.bytes.truncate(new_len);
        }
    }

    /// Retains only the characters specified by the predicate.
    pub fn retain<F: FnMut(char) -> bool>(&mut self, mut f: F) {
        let mut result = Vec::with_capacity(self.len());
        let mut offset = 0;

        while offset < self.bytes.len() {
            if let Some((c, next)) = E::decode_char_at(&self.bytes, offset) {
                if f(c) {
                    result.extend_from_slice(&self.bytes[offset..next]);
                }
                offset = next;
            } else {
                break;
            }
        }

        self.bytes = result;
    }

    /// Splits the string into two at the given byte index.
    ///
    /// Returns a newly allocated `String`. `self` contains bytes `[0, at)`, and
    /// the returned `String` contains bytes `[at, len)`.
    ///
    /// # Panics
    ///
    /// Panics if `at` is not on a `char` boundary, or if it is beyond the last
    /// code point of the string.
    pub fn split_off(&mut self, at: usize) -> Self {
        assert!(self.is_char_boundary(at), "at is not a char boundary");
        let other = self.bytes.split_off(at);
        Self {
            bytes: other,
            _marker: PhantomData,
        }
    }

    /// Creates a draining iterator that removes the specified range in the `String`
    /// and yields the removed `char`s.
    ///
    /// # Panics
    ///
    /// Panics if the starting point or end point do not lie on a `char` boundary,
    /// or if they're out of bounds.
    pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> Drain<'_, E> {
        let start = match range.start_bound() {
            core::ops::Bound::Included(&n) => n,
            core::ops::Bound::Excluded(&n) => n + 1,
            core::ops::Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            core::ops::Bound::Included(&n) => n + 1,
            core::ops::Bound::Excluded(&n) => n,
            core::ops::Bound::Unbounded => self.len(),
        };

        assert!(self.is_char_boundary(start), "start is not a char boundary");
        assert!(self.is_char_boundary(end), "end is not a char boundary");
        assert!(start <= end && end <= self.len(), "range out of bounds");

        Drain::new(self, start, end)
    }

    /// Replaces the specified range in the string with the given string.
    ///
    /// # Panics
    ///
    /// Panics if the starting point or end point do not lie on a `char` boundary,
    /// or if they're out of bounds.
    pub fn replace_range<R: RangeBounds<usize>>(&mut self, range: R, replace_with: &Str<E>) {
        let start = match range.start_bound() {
            core::ops::Bound::Included(&n) => n,
            core::ops::Bound::Excluded(&n) => n + 1,
            core::ops::Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            core::ops::Bound::Included(&n) => n + 1,
            core::ops::Bound::Excluded(&n) => n,
            core::ops::Bound::Unbounded => self.len(),
        };

        assert!(self.is_char_boundary(start), "start is not a char boundary");
        assert!(self.is_char_boundary(end), "end is not a char boundary");
        assert!(start <= end && end <= self.len(), "range out of bounds");

        let replace_bytes = replace_with.as_bytes();
        let replace_len = replace_bytes.len();
        let range_len = end - start;

        if replace_len > range_len {
            // Need to grow
            let additional = replace_len - range_len;
            self.bytes.reserve(additional);
            let old_len = self.bytes.len();
            unsafe {
                self.bytes.set_len(old_len + additional);
                // Move bytes after the range
                core::ptr::copy(
                    self.bytes.as_ptr().add(end),
                    self.bytes.as_mut_ptr().add(start + replace_len),
                    old_len - end,
                );
            }
        } else if replace_len < range_len {
            // Need to shrink
            let removed = range_len - replace_len;
            unsafe {
                // Move bytes after the range
                core::ptr::copy(
                    self.bytes.as_ptr().add(end),
                    self.bytes.as_mut_ptr().add(start + replace_len),
                    self.bytes.len() - end,
                );
                self.bytes.set_len(self.bytes.len() - removed);
            }
        }

        // Copy in the replacement
        self.bytes[start..start + replace_len].copy_from_slice(replace_bytes);
    }

    // === Conversion ===

    /// Converts a `String` into a byte vector.
    #[inline]
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    /// Extracts a string slice containing the entire `String`.
    #[inline]
    pub fn as_str(&self) -> &Str<E> {
        // SAFETY: self.bytes is always valid for encoding E
        unsafe { Str::from_bytes_unchecked(&self.bytes) }
    }

    /// Extracts a mutable string slice containing the entire `String`.
    #[inline]
    pub fn as_mut_str(&mut self) -> &mut Str<E> {
        // SAFETY: self.bytes is always valid for encoding E
        unsafe { Str::from_bytes_unchecked_mut(&mut self.bytes) }
    }

    /// Returns a byte slice of this `String`'s contents.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns a mutable reference to the contents of this `String`.
    ///
    /// # Safety
    ///
    /// This function is unsafe because the returned `&mut Vec` allows writing
    /// bytes which are not valid for this encoding.
    #[inline]
    pub unsafe fn as_mut_vec(&mut self) -> &mut Vec<u8> {
        &mut self.bytes
    }

    /// Converts this string to a `std::string::String` (UTF-8).
    ///
    /// For `String<Utf8>`, consider using `Into<std::string::String>` instead
    /// for a zero-copy conversion.
    ///
    /// For other encodings, this transcodes to UTF-8 by iterating over characters.
    #[inline]
    pub fn to_std(&self) -> std::string::String {
        self.chars().collect()
    }

    // === Box conversion ===

    /// Converts this `String` into a `Box<Str<E>>`.
    #[inline]
    pub fn into_boxed_str(self) -> Box<Str<E>> {
        let boxed_bytes = self.bytes.into_boxed_slice();
        // SAFETY: self.bytes was valid, and Box<[u8]> has the same layout as Box<Str<E>>
        unsafe { Box::from_raw(Box::into_raw(boxed_bytes) as *mut Str<E>) }
    }

    // === Leak ===

    /// Consumes and leaks the `String`, returning a mutable reference to the contents.
    #[inline]
    pub fn leak(self) -> &'static mut Str<E> {
        let leaked = self.bytes.leak();
        // SAFETY: leaked bytes were valid
        unsafe { Str::from_bytes_unchecked_mut(leaked) }
    }
}

// === Trait implementations ===

impl<E: Encoding> Clone for String<E> {
    fn clone(&self) -> Self {
        Self {
            bytes: self.bytes.clone(),
            _marker: PhantomData,
        }
    }
}

impl<E: Encoding> Default for String<E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<E: Encoding> Deref for String<E> {
    type Target = Str<E>;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<E: Encoding> DerefMut for String<E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_str()
    }
}

impl<E: Encoding> Borrow<Str<E>> for String<E> {
    fn borrow(&self) -> &Str<E> {
        self.as_str()
    }
}

impl<E: Encoding> BorrowMut<Str<E>> for String<E> {
    fn borrow_mut(&mut self) -> &mut Str<E> {
        self.as_mut_str()
    }
}

impl<E: Encoding> fmt::Debug for String<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl<E: Encoding> fmt::Display for String<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl<E: Encoding> Hash for String<E> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

impl<E: Encoding> PartialEq for String<E> {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl<E: Encoding> Eq for String<E> {}

impl<E: Encoding> PartialEq<Str<E>> for String<E> {
    fn eq(&self, other: &Str<E>) -> bool {
        self.as_str() == other
    }
}

impl<E: Encoding> PartialEq<&Str<E>> for String<E> {
    fn eq(&self, other: &&Str<E>) -> bool {
        self.as_str() == *other
    }
}

impl<E: Encoding> PartialEq<String<E>> for Str<E> {
    fn eq(&self, other: &String<E>) -> bool {
        self == other.as_str()
    }
}

impl<E: Encoding> PartialEq<String<E>> for &Str<E> {
    fn eq(&self, other: &String<E>) -> bool {
        *self == other.as_str()
    }
}

impl<E: Encoding> PartialOrd for String<E> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<E: Encoding> Ord for String<E> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl<E: Encoding> FromIterator<char> for String<E> {
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> Self {
        let mut s = String::new();
        s.extend(iter);
        s
    }
}

impl<'a, E: Encoding> FromIterator<&'a char> for String<E> {
    fn from_iter<I: IntoIterator<Item = &'a char>>(iter: I) -> Self {
        let mut s = String::new();
        s.extend(iter.into_iter().copied());
        s
    }
}

impl<E: Encoding> Extend<char> for String<E> {
    fn extend<I: IntoIterator<Item = char>>(&mut self, iter: I) {
        for c in iter {
            self.push(c);
        }
    }
}

impl<'a, E: Encoding> Extend<&'a char> for String<E> {
    fn extend<I: IntoIterator<Item = &'a char>>(&mut self, iter: I) {
        self.extend(iter.into_iter().copied());
    }
}

impl<'a, E: Encoding> Extend<&'a Str<E>> for String<E> {
    fn extend<I: IntoIterator<Item = &'a Str<E>>>(&mut self, iter: I) {
        for s in iter {
            self.push_str(s);
        }
    }
}

impl<E: Encoding> Extend<String<E>> for String<E> {
    fn extend<I: IntoIterator<Item = String<E>>>(&mut self, iter: I) {
        for s in iter {
            self.push_str(&s);
        }
    }
}

impl<E: Encoding> AsRef<Str<E>> for String<E> {
    fn as_ref(&self) -> &Str<E> {
        self.as_str()
    }
}

impl<E: Encoding> AsRef<[u8]> for String<E> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<E: Encoding> AsMut<Str<E>> for String<E> {
    fn as_mut(&mut self) -> &mut Str<E> {
        self.as_mut_str()
    }
}

impl<E: Encoding> From<&Str<E>> for String<E> {
    fn from(s: &Str<E>) -> Self {
        Self {
            bytes: s.as_bytes().to_vec(),
            _marker: PhantomData,
        }
    }
}

impl<E: Encoding> From<&mut Str<E>> for String<E> {
    fn from(s: &mut Str<E>) -> Self {
        Self {
            bytes: s.as_bytes().to_vec(),
            _marker: PhantomData,
        }
    }
}

impl<E: Encoding> From<Box<Str<E>>> for String<E> {
    fn from(boxed: Box<Str<E>>) -> Self {
        // SAFETY: Box<Str<E>> has the same layout as Box<[u8]>
        let boxed_bytes: Box<[u8]> = unsafe { Box::from_raw(Box::into_raw(boxed) as *mut [u8]) };
        Self {
            bytes: boxed_bytes.into_vec(),
            _marker: PhantomData,
        }
    }
}

impl<E: Encoding> From<char> for String<E> {
    fn from(c: char) -> Self {
        let mut s = String::new();
        s.push(c);
        s
    }
}

// Transcoding: From<&Str<F>> for String<E> where E != F
// This is implemented in lib.rs to avoid circular dependencies

impl<E: Encoding> fmt::Write for String<E> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        // Convert from UTF-8 str to our encoding
        for c in s.chars() {
            self.push(c);
        }
        Ok(())
    }

    fn write_char(&mut self, c: char) -> fmt::Result {
        self.push(c);
        Ok(())
    }
}

impl<'a, E: Encoding> Add<&'a Str<E>> for String<E> {
    type Output = String<E>;

    fn add(mut self, other: &'a Str<E>) -> String<E> {
        self.push_str(other);
        self
    }
}

impl<'a, E: Encoding> AddAssign<&'a Str<E>> for String<E> {
    fn add_assign(&mut self, other: &'a Str<E>) {
        self.push_str(other);
    }
}

// === Index implementations ===

impl<E: Encoding> Index<RangeFull> for String<E> {
    type Output = Str<E>;

    fn index(&self, _: RangeFull) -> &Self::Output {
        self.as_str()
    }
}

impl<E: Encoding> Index<Range<usize>> for String<E> {
    type Output = Str<E>;

    fn index(&self, index: Range<usize>) -> &Self::Output {
        &self.as_str()[index]
    }
}

impl<E: Encoding> Index<RangeFrom<usize>> for String<E> {
    type Output = Str<E>;

    fn index(&self, index: RangeFrom<usize>) -> &Self::Output {
        &self.as_str()[index]
    }
}

impl<E: Encoding> Index<RangeTo<usize>> for String<E> {
    type Output = Str<E>;

    fn index(&self, index: RangeTo<usize>) -> &Self::Output {
        &self.as_str()[index]
    }
}

impl<E: Encoding> Index<RangeInclusive<usize>> for String<E> {
    type Output = Str<E>;

    fn index(&self, index: RangeInclusive<usize>) -> &Self::Output {
        &self.as_str()[index]
    }
}

impl<E: Encoding> Index<RangeToInclusive<usize>> for String<E> {
    type Output = Str<E>;

    fn index(&self, index: RangeToInclusive<usize>) -> &Self::Output {
        &self.as_str()[index]
    }
}

impl<E: Encoding> IndexMut<RangeFull> for String<E> {
    fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
        self.as_mut_str()
    }
}

impl<E: Encoding> IndexMut<Range<usize>> for String<E> {
    fn index_mut(&mut self, index: Range<usize>) -> &mut Self::Output {
        &mut self.as_mut_str()[index]
    }
}

impl<E: Encoding> IndexMut<RangeFrom<usize>> for String<E> {
    fn index_mut(&mut self, index: RangeFrom<usize>) -> &mut Self::Output {
        &mut self.as_mut_str()[index]
    }
}

impl<E: Encoding> IndexMut<RangeTo<usize>> for String<E> {
    fn index_mut(&mut self, index: RangeTo<usize>) -> &mut Self::Output {
        &mut self.as_mut_str()[index]
    }
}

impl<E: Encoding> IndexMut<RangeInclusive<usize>> for String<E> {
    fn index_mut(&mut self, index: RangeInclusive<usize>) -> &mut Self::Output {
        &mut self.as_mut_str()[index]
    }
}

impl<E: Encoding> IndexMut<RangeToInclusive<usize>> for String<E> {
    fn index_mut(&mut self, index: RangeToInclusive<usize>) -> &mut Self::Output {
        &mut self.as_mut_str()[index]
    }
}

impl<E: Encoding> core::str::FromStr for String<E> {
    type Err = crate::error::TranscodeError;

    /// Parses a `&str` into a `String<E>` by transcoding from UTF-8.
    ///
    /// For universal encodings (UTF-8, UTF-16, UTF-32, GB18030), this always succeeds.
    /// For limited encodings (like codepages), this may fail if the string contains
    /// characters that cannot be represented in the target encoding.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut result = String::new();
        let mut buf = [0u8; 8]; // Max bytes for any encoding
        for (index, c) in s.chars().enumerate() {
            if let Some(len) = E::try_encode_char(c, &mut buf) {
                result.bytes.extend_from_slice(&buf[..len]);
            } else {
                return Err(crate::error::TranscodeError::new(c, index));
            }
        }
        Ok(result)
    }
}
