//! Null-terminated borrowed string slice type.
//!
//! This module provides [`CStr<E>`], a borrowed reference to a null-terminated
//! string in any encoding. It is analogous to [`std::ffi::CStr`] but supports
//! arbitrary character encodings.

use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ptr;

use crate::Str;
use crate::encoding::Encoding;
use crate::error::FromBytesWithNulError;
use crate::iter::Chars;

/// A borrowed reference to a null-terminated string in encoding `E`.
///
/// This type represents a borrowed reference to a null-terminated array of bytes
/// that are valid in the specified encoding. It is the encoding-generic equivalent
/// of [`std::ffi::CStr`].
///
/// # Null Terminator Width
///
/// The null terminator width depends on the encoding:
/// - UTF-8 and single-byte encodings: 1 byte (`0x00`)
/// - UTF-16: 2 bytes (`0x0000`)
/// - UTF-32: 4 bytes (`0x00000000`)
///
/// # Interior Nulls
///
/// Like [`std::ffi::CStr`], this type does not permit interior null characters.
/// The string is considered to end at the first null character encountered.
///
/// # Example
///
/// ```
/// use stringly::{CStr, Utf8};
///
/// let bytes = b"hello\0";
/// let cstr = CStr::<Utf8>::from_bytes_with_nul(bytes).unwrap();
/// assert_eq!(cstr.as_str().len(), 5);
/// ```
#[repr(transparent)]
pub struct CStr<E: Encoding> {
    _marker: PhantomData<E>,
    /// The underlying byte slice, including the null terminator.
    bytes: [u8],
}

impl<E: Encoding> CStr<E> {
    /// Creates a `CStr` from a byte slice containing a null terminator.
    ///
    /// The slice must:
    /// - End with the appropriate null terminator for the encoding
    /// - Not contain any interior null characters
    /// - Be valid for the encoding
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The slice does not end with a null terminator
    /// - The slice contains interior null characters
    /// - The slice is not valid for the encoding
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CStr, Utf8};
    ///
    /// let cstr = CStr::<Utf8>::from_bytes_with_nul(b"hello\0").unwrap();
    /// assert_eq!(cstr.len(), 5);
    ///
    /// // Missing null terminator
    /// assert!(CStr::<Utf8>::from_bytes_with_nul(b"hello").is_err());
    ///
    /// // Interior null
    /// assert!(CStr::<Utf8>::from_bytes_with_nul(b"hel\0lo\0").is_err());
    /// ```
    pub fn from_bytes_with_nul(bytes: &[u8]) -> Result<&Self, FromBytesWithNulError> {
        let null_len = E::NULL_LEN;

        // Check minimum length (at least null terminator)
        if bytes.len() < null_len {
            return Err(FromBytesWithNulError::not_nul_terminated());
        }

        // Check that bytes end with null terminator
        let terminator_start = bytes.len() - null_len;
        let terminator = &bytes[terminator_start..];
        if !is_null_bytes::<E>(terminator) {
            return Err(FromBytesWithNulError::not_nul_terminated());
        }

        // Validate encoding of content (excluding null terminator)
        let content = &bytes[..terminator_start];
        if let Err(e) = E::validate(content) {
            return Err(FromBytesWithNulError::invalid_encoding(e));
        }

        // Check for interior nulls by iterating through characters
        let str_content = unsafe { Str::<E>::from_bytes_unchecked(content) };
        for (idx, c) in str_content.char_indices() {
            if c == '\0' {
                return Err(FromBytesWithNulError::interior_nul(idx));
            }
        }

        // SAFETY: We've validated the bytes
        Ok(unsafe { Self::from_bytes_with_nul_unchecked(bytes) })
    }

    /// Creates a `CStr` from a byte slice without checking validity.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - The slice ends with the appropriate null terminator for the encoding
    /// - The slice does not contain interior null characters
    /// - The slice is valid for the encoding
    #[inline]
    pub const unsafe fn from_bytes_with_nul_unchecked(bytes: &[u8]) -> &Self {
        // SAFETY: CStr<E> is repr(transparent) over [u8]
        unsafe { &*(ptr::from_ref(bytes) as *const Self) }
    }

    /// Creates a mutable `CStr` from a byte slice without checking validity.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - The slice ends with the appropriate null terminator for the encoding
    /// - The slice does not contain interior null characters
    /// - The slice is valid for the encoding
    /// - Mutations maintain these invariants
    #[inline]
    pub unsafe fn from_bytes_with_nul_unchecked_mut(bytes: &mut [u8]) -> &mut Self {
        // SAFETY: CStr<E> is repr(transparent) over [u8]
        unsafe { &mut *(ptr::from_mut(bytes) as *mut Self) }
    }

    /// Creates a `CStr` from a pointer to a null-terminated string.
    ///
    /// This function scans for the null terminator starting from `ptr`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a valid null-terminated string in encoding `E`
    /// - The string must not contain interior null characters
    /// - The memory must be valid for reads up to and including the null terminator
    /// - The returned lifetime is unbounded - caller must ensure the data outlives it
    #[inline]
    pub unsafe fn from_ptr<'a>(ptr: *const u8) -> &'a Self {
        unsafe {
            let len = Self::strlen(ptr);
            let bytes = core::slice::from_raw_parts(ptr, len + E::NULL_LEN);
            Self::from_bytes_with_nul_unchecked(bytes)
        }
    }

    /// Calculates the length of a null-terminated string (excluding null).
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a valid null-terminated string in encoding `E`
    /// - The memory must be valid for reads up to and including the null terminator
    pub(crate) unsafe fn strlen(ptr: *const u8) -> usize {
        let null_len = E::NULL_LEN;
        let mut len = 0;

        loop {
            let candidate = unsafe { core::slice::from_raw_parts(ptr.add(len), null_len) };
            if is_null_bytes::<E>(candidate) {
                return len;
            }
            // Move forward by one code unit
            len += null_len;
        }
    }

    /// Returns the inner byte slice, excluding the null terminator.
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CStr, Utf8};
    ///
    /// let cstr = CStr::<Utf8>::from_bytes_with_nul(b"hello\0").unwrap();
    /// assert_eq!(cstr.as_bytes(), b"hello");
    /// ```
    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        let len = self.bytes.len() - E::NULL_LEN;
        // SAFETY: We know the slice is at least NULL_LEN bytes
        unsafe { core::slice::from_raw_parts(self.bytes.as_ptr(), len) }
    }

    /// Returns the inner byte slice, including the null terminator.
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CStr, Utf8};
    ///
    /// let cstr = CStr::<Utf8>::from_bytes_with_nul(b"hello\0").unwrap();
    /// assert_eq!(cstr.as_bytes_with_nul(), b"hello\0");
    /// ```
    #[inline]
    pub const fn as_bytes_with_nul(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns a raw pointer to the string's buffer.
    ///
    /// The returned pointer points to the start of the string and is valid
    /// up to and including the null terminator.
    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        self.bytes.as_ptr()
    }

    /// Returns this C string as a `Str<E>` slice, excluding the null terminator.
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CStr, Utf8};
    ///
    /// let cstr = CStr::<Utf8>::from_bytes_with_nul(b"hello\0").unwrap();
    /// let s = cstr.as_str();
    /// assert_eq!(s.len(), 5);
    /// ```
    #[inline]
    pub fn as_str(&self) -> &Str<E> {
        // SAFETY: We've already validated the encoding during construction
        unsafe { Str::from_bytes_unchecked(self.as_bytes()) }
    }

    /// Returns the length of the string in bytes, excluding the null terminator.
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CStr, Utf8};
    ///
    /// let cstr = CStr::<Utf8>::from_bytes_with_nul(b"hello\0").unwrap();
    /// assert_eq!(cstr.len(), 5);
    /// ```
    #[inline]
    pub const fn len(&self) -> usize {
        self.bytes.len() - E::NULL_LEN
    }

    /// Returns `true` if the string has length 0 (only contains the null terminator).
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CStr, Utf8};
    ///
    /// let empty = CStr::<Utf8>::from_bytes_with_nul(b"\0").unwrap();
    /// assert!(empty.is_empty());
    ///
    /// let hello = CStr::<Utf8>::from_bytes_with_nul(b"hello\0").unwrap();
    /// assert!(!hello.is_empty());
    /// ```
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns an iterator over the characters of this string.
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CStr, Utf8};
    ///
    /// let cstr = CStr::<Utf8>::from_bytes_with_nul(b"hi\0").unwrap();
    /// let chars: Vec<_> = cstr.chars().collect();
    /// assert_eq!(chars, vec!['h', 'i']);
    /// ```
    #[inline]
    pub fn chars(&self) -> Chars<'_, E> {
        self.as_str().chars()
    }

    /// Returns the number of characters in the string.
    ///
    /// This is an O(n) operation as it requires iterating through all characters.
    #[inline]
    pub fn count_chars(&self) -> usize {
        self.chars().count()
    }

    /// Returns a reference to an empty C string.
    ///
    /// This returns a reference to a static empty C string (just the null terminator).
    #[inline]
    pub fn empty() -> &'static Self {
        // SAFETY: An array of NULL_LEN zeros is a valid empty CStr
        static EMPTY_UTF8: [u8; 1] = [0];
        static EMPTY_UTF16: [u8; 2] = [0, 0];
        static EMPTY_UTF32: [u8; 4] = [0, 0, 0, 0];

        unsafe {
            match E::NULL_LEN {
                1 => Self::from_bytes_with_nul_unchecked(&EMPTY_UTF8),
                2 => Self::from_bytes_with_nul_unchecked(&EMPTY_UTF16),
                4 => Self::from_bytes_with_nul_unchecked(&EMPTY_UTF32),
                _ => unreachable!(),
            }
        }
    }
}

/// Check if the given bytes represent a null character for the encoding.
#[inline]
fn is_null_bytes<E: Encoding>(bytes: &[u8]) -> bool {
    bytes.len() == E::NULL_LEN && bytes.iter().all(|&b| b == 0)
}

// === Trait implementations ===

impl<E: Encoding> fmt::Debug for CStr<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CStr<{}>", E::NAME)?;
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl<E: Encoding> fmt::Display for CStr<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl<E: Encoding> PartialEq for CStr<E> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl<E: Encoding> Eq for CStr<E> {}

impl<E: Encoding> PartialOrd for CStr<E> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<E: Encoding> Ord for CStr<E> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl<E: Encoding> Hash for CStr<E> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_bytes().hash(state);
    }
}

impl<E: Encoding> AsRef<Str<E>> for CStr<E> {
    #[inline]
    fn as_ref(&self) -> &Str<E> {
        self.as_str()
    }
}

impl<E: Encoding> AsRef<[u8]> for CStr<E> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<E: Encoding> core::borrow::Borrow<Str<E>> for CStr<E> {
    #[inline]
    fn borrow(&self) -> &Str<E> {
        self.as_str()
    }
}

// Index implementations for ranges
impl<E: Encoding> core::ops::Index<core::ops::RangeFull> for CStr<E> {
    type Output = Str<E>;

    #[inline]
    fn index(&self, _: core::ops::RangeFull) -> &Self::Output {
        self.as_str()
    }
}

// =============================================================================
// Compile-time CStr macros
// =============================================================================

/// Creates a `&'static CStr<Utf8>` from a string literal at compile time.
///
/// This macro appends a null terminator to the string literal and returns
/// a static reference to a `CStr<Utf8>`.
///
/// # Example
///
/// ```
/// use stringly::{utf8_cstr, Utf8CStr};
///
/// static HELLO: &Utf8CStr = utf8_cstr!("hello");
/// assert_eq!(HELLO.as_bytes(), b"hello");
/// assert_eq!(HELLO.as_bytes_with_nul(), b"hello\0");
/// ```
#[macro_export]
macro_rules! utf8_cstr {
    ($s:literal) => {{
        const BYTES: &[u8] = concat!($s, "\0").as_bytes();
        // SAFETY: concat! ensures null terminator, literal is valid UTF-8, no interior nulls
        unsafe { $crate::CStr::<$crate::Utf8>::from_bytes_with_nul_unchecked(BYTES) }
    }};
}

// =============================================================================
// Const encoders for UTF-16/32 macros
// =============================================================================

/// Const encoder for UTF-16LE strings.
#[doc(hidden)]
pub struct Utf16LeEncoder;

impl Utf16LeEncoder {
    /// Calculate the output length in bytes for encoding a UTF-8 string to UTF-16LE with null.
    pub const fn output_len(s: &str) -> usize {
        let bytes = s.as_bytes();
        let mut i = 0;
        let mut len = 0;
        while i < bytes.len() {
            let b = bytes[i];
            if b < 0x80 {
                len += 2; // ASCII -> 1 code unit
                i += 1;
            } else if b < 0xE0 {
                len += 2; // 2-byte UTF-8 -> 1 code unit
                i += 2;
            } else if b < 0xF0 {
                len += 2; // 3-byte UTF-8 -> 1 code unit
                i += 3;
            } else {
                len += 4; // 4-byte UTF-8 -> surrogate pair (2 code units)
                i += 4;
            }
        }
        len + 2 // Plus null terminator (2 bytes)
    }

    /// Encode a UTF-8 string to UTF-16LE bytes with null terminator.
    pub const fn encode<const N: usize>(s: &str) -> [u8; N] {
        let bytes = s.as_bytes();
        let mut out = [0u8; N];
        let mut i = 0;
        let mut o = 0;

        while i < bytes.len() {
            let b = bytes[i];
            let (cp, advance) = if b < 0x80 {
                (b as u32, 1)
            } else if b < 0xE0 {
                let cp = ((b as u32 & 0x1F) << 6) | (bytes[i + 1] as u32 & 0x3F);
                (cp, 2)
            } else if b < 0xF0 {
                let cp = ((b as u32 & 0x0F) << 12)
                    | ((bytes[i + 1] as u32 & 0x3F) << 6)
                    | (bytes[i + 2] as u32 & 0x3F);
                (cp, 3)
            } else {
                let cp = ((b as u32 & 0x07) << 18)
                    | ((bytes[i + 1] as u32 & 0x3F) << 12)
                    | ((bytes[i + 2] as u32 & 0x3F) << 6)
                    | (bytes[i + 3] as u32 & 0x3F);
                (cp, 4)
            };

            if cp <= 0xFFFF {
                // BMP character
                out[o] = cp as u8;
                out[o + 1] = (cp >> 8) as u8;
                o += 2;
            } else {
                // Surrogate pair
                let cp = cp - 0x10000;
                let high = 0xD800 + (cp >> 10);
                let low = 0xDC00 + (cp & 0x3FF);
                out[o] = high as u8;
                out[o + 1] = (high >> 8) as u8;
                out[o + 2] = low as u8;
                out[o + 3] = (low >> 8) as u8;
                o += 4;
            }
            i += advance;
        }
        // Null terminator already zero-initialized
        out
    }
}

/// Const encoder for UTF-16BE strings.
#[doc(hidden)]
pub struct Utf16BeEncoder;

impl Utf16BeEncoder {
    /// Calculate the output length in bytes for encoding a UTF-8 string to UTF-16BE with null.
    pub const fn output_len(s: &str) -> usize {
        Utf16LeEncoder::output_len(s) // Same length calculation
    }

    /// Encode a UTF-8 string to UTF-16BE bytes with null terminator.
    pub const fn encode<const N: usize>(s: &str) -> [u8; N] {
        let bytes = s.as_bytes();
        let mut out = [0u8; N];
        let mut i = 0;
        let mut o = 0;

        while i < bytes.len() {
            let b = bytes[i];
            let (cp, advance) = if b < 0x80 {
                (b as u32, 1)
            } else if b < 0xE0 {
                let cp = ((b as u32 & 0x1F) << 6) | (bytes[i + 1] as u32 & 0x3F);
                (cp, 2)
            } else if b < 0xF0 {
                let cp = ((b as u32 & 0x0F) << 12)
                    | ((bytes[i + 1] as u32 & 0x3F) << 6)
                    | (bytes[i + 2] as u32 & 0x3F);
                (cp, 3)
            } else {
                let cp = ((b as u32 & 0x07) << 18)
                    | ((bytes[i + 1] as u32 & 0x3F) << 12)
                    | ((bytes[i + 2] as u32 & 0x3F) << 6)
                    | (bytes[i + 3] as u32 & 0x3F);
                (cp, 4)
            };

            if cp <= 0xFFFF {
                // BMP character (big-endian)
                out[o] = (cp >> 8) as u8;
                out[o + 1] = cp as u8;
                o += 2;
            } else {
                // Surrogate pair (big-endian)
                let cp = cp - 0x10000;
                let high = 0xD800 + (cp >> 10);
                let low = 0xDC00 + (cp & 0x3FF);
                out[o] = (high >> 8) as u8;
                out[o + 1] = high as u8;
                out[o + 2] = (low >> 8) as u8;
                out[o + 3] = low as u8;
                o += 4;
            }
            i += advance;
        }
        out
    }
}

/// Const encoder for UTF-32LE strings.
#[doc(hidden)]
pub struct Utf32LeEncoder;

impl Utf32LeEncoder {
    /// Calculate the output length in bytes for encoding a UTF-8 string to UTF-32LE with null.
    pub const fn output_len(s: &str) -> usize {
        let bytes = s.as_bytes();
        let mut i = 0;
        let mut len = 0;
        while i < bytes.len() {
            let b = bytes[i];
            len += 4; // Every character is 4 bytes
            if b < 0x80 {
                i += 1;
            } else if b < 0xE0 {
                i += 2;
            } else if b < 0xF0 {
                i += 3;
            } else {
                i += 4;
            }
        }
        len + 4 // Plus null terminator (4 bytes)
    }

    /// Encode a UTF-8 string to UTF-32LE bytes with null terminator.
    pub const fn encode<const N: usize>(s: &str) -> [u8; N] {
        let bytes = s.as_bytes();
        let mut out = [0u8; N];
        let mut i = 0;
        let mut o = 0;

        while i < bytes.len() {
            let b = bytes[i];
            let (cp, advance) = if b < 0x80 {
                (b as u32, 1)
            } else if b < 0xE0 {
                let cp = ((b as u32 & 0x1F) << 6) | (bytes[i + 1] as u32 & 0x3F);
                (cp, 2)
            } else if b < 0xF0 {
                let cp = ((b as u32 & 0x0F) << 12)
                    | ((bytes[i + 1] as u32 & 0x3F) << 6)
                    | (bytes[i + 2] as u32 & 0x3F);
                (cp, 3)
            } else {
                let cp = ((b as u32 & 0x07) << 18)
                    | ((bytes[i + 1] as u32 & 0x3F) << 12)
                    | ((bytes[i + 2] as u32 & 0x3F) << 6)
                    | (bytes[i + 3] as u32 & 0x3F);
                (cp, 4)
            };

            // Little-endian: least significant byte first
            out[o] = cp as u8;
            out[o + 1] = (cp >> 8) as u8;
            out[o + 2] = (cp >> 16) as u8;
            out[o + 3] = (cp >> 24) as u8;
            o += 4;
            i += advance;
        }
        out
    }
}

/// Const encoder for UTF-32BE strings.
#[doc(hidden)]
pub struct Utf32BeEncoder;

impl Utf32BeEncoder {
    /// Calculate the output length in bytes for encoding a UTF-8 string to UTF-32BE with null.
    pub const fn output_len(s: &str) -> usize {
        Utf32LeEncoder::output_len(s) // Same length calculation
    }

    /// Encode a UTF-8 string to UTF-32BE bytes with null terminator.
    pub const fn encode<const N: usize>(s: &str) -> [u8; N] {
        let bytes = s.as_bytes();
        let mut out = [0u8; N];
        let mut i = 0;
        let mut o = 0;

        while i < bytes.len() {
            let b = bytes[i];
            let (cp, advance) = if b < 0x80 {
                (b as u32, 1)
            } else if b < 0xE0 {
                let cp = ((b as u32 & 0x1F) << 6) | (bytes[i + 1] as u32 & 0x3F);
                (cp, 2)
            } else if b < 0xF0 {
                let cp = ((b as u32 & 0x0F) << 12)
                    | ((bytes[i + 1] as u32 & 0x3F) << 6)
                    | (bytes[i + 2] as u32 & 0x3F);
                (cp, 3)
            } else {
                let cp = ((b as u32 & 0x07) << 18)
                    | ((bytes[i + 1] as u32 & 0x3F) << 12)
                    | ((bytes[i + 2] as u32 & 0x3F) << 6)
                    | (bytes[i + 3] as u32 & 0x3F);
                (cp, 4)
            };

            // Big-endian: most significant byte first
            out[o] = (cp >> 24) as u8;
            out[o + 1] = (cp >> 16) as u8;
            out[o + 2] = (cp >> 8) as u8;
            out[o + 3] = cp as u8;
            o += 4;
            i += advance;
        }
        out
    }
}

/// Creates a `&'static CStr<Utf16Le>` from a string literal at compile time.
///
/// # Example
///
/// ```
/// use stringly::{utf16le_cstr, Utf16LeCStr};
///
/// static HELLO: &Utf16LeCStr = utf16le_cstr!("hello");
/// assert_eq!(HELLO.len(), 10); // 5 chars * 2 bytes each
/// ```
#[cfg(feature = "utf16")]
#[macro_export]
macro_rules! utf16le_cstr {
    ($s:literal) => {{
        const INPUT: &str = $s;
        const LEN: usize = $crate::cstr::Utf16LeEncoder::output_len(INPUT);
        const BYTES: [u8; LEN] = $crate::cstr::Utf16LeEncoder::encode(INPUT);
        // SAFETY: Encoder produces valid UTF-16LE with null terminator
        unsafe { $crate::CStr::<$crate::Utf16Le>::from_bytes_with_nul_unchecked(&BYTES) }
    }};
}

/// Creates a `&'static CStr<Utf16Be>` from a string literal at compile time.
///
/// # Example
///
/// ```
/// use stringly::{utf16be_cstr, Utf16BeCStr};
///
/// static HELLO: &Utf16BeCStr = utf16be_cstr!("hello");
/// assert_eq!(HELLO.len(), 10); // 5 chars * 2 bytes each
/// ```
#[cfg(feature = "utf16")]
#[macro_export]
macro_rules! utf16be_cstr {
    ($s:literal) => {{
        const INPUT: &str = $s;
        const LEN: usize = $crate::cstr::Utf16BeEncoder::output_len(INPUT);
        const BYTES: [u8; LEN] = $crate::cstr::Utf16BeEncoder::encode(INPUT);
        // SAFETY: Encoder produces valid UTF-16BE with null terminator
        unsafe { $crate::CStr::<$crate::Utf16Be>::from_bytes_with_nul_unchecked(&BYTES) }
    }};
}

/// Creates a `&'static CStr<Utf32Le>` from a string literal at compile time.
///
/// # Example
///
/// ```
/// use stringly::{utf32le_cstr, Utf32LeCStr};
///
/// static HELLO: &Utf32LeCStr = utf32le_cstr!("hello");
/// assert_eq!(HELLO.len(), 20); // 5 chars * 4 bytes each
/// ```
#[cfg(feature = "utf32")]
#[macro_export]
macro_rules! utf32le_cstr {
    ($s:literal) => {{
        const INPUT: &str = $s;
        const LEN: usize = $crate::cstr::Utf32LeEncoder::output_len(INPUT);
        const BYTES: [u8; LEN] = $crate::cstr::Utf32LeEncoder::encode(INPUT);
        // SAFETY: Encoder produces valid UTF-32LE with null terminator
        unsafe { $crate::CStr::<$crate::Utf32Le>::from_bytes_with_nul_unchecked(&BYTES) }
    }};
}

/// Creates a `&'static CStr<Utf32Be>` from a string literal at compile time.
///
/// # Example
///
/// ```
/// use stringly::{utf32be_cstr, Utf32BeCStr};
///
/// static HELLO: &Utf32BeCStr = utf32be_cstr!("hello");
/// assert_eq!(HELLO.len(), 20); // 5 chars * 4 bytes each
/// ```
#[cfg(feature = "utf32")]
#[macro_export]
macro_rules! utf32be_cstr {
    ($s:literal) => {{
        const INPUT: &str = $s;
        const LEN: usize = $crate::cstr::Utf32BeEncoder::output_len(INPUT);
        const BYTES: [u8; LEN] = $crate::cstr::Utf32BeEncoder::encode(INPUT);
        // SAFETY: Encoder produces valid UTF-32BE with null terminator
        unsafe { $crate::CStr::<$crate::Utf32Be>::from_bytes_with_nul_unchecked(&BYTES) }
    }};
}
