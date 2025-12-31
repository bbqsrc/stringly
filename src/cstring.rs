//! Null-terminated owned string type.
//!
//! This module provides [`CString<E>`], an owned null-terminated string in any
//! encoding. It is analogous to [`alloc::ffi::CString`] but supports arbitrary
//! character encodings.

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::Deref;

use crate::Str;
use crate::String;
use crate::cstr::CStr;
use crate::encoding::Encoding;
use crate::error::{FromBytesWithNulError, FromBytesWithNulVecError};
use crate::iter::Chars;

/// An owned null-terminated string in encoding `E`.
///
/// This type represents an owned, null-terminated string that is valid in the
/// specified encoding. It is the encoding-generic equivalent of [`alloc::ffi::CString`].
///
/// `CString<E>` dereferences to [`CStr<E>`], providing access to all borrowed
/// string operations.
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
/// Like [`alloc::ffi::CString`], this type does not permit interior null characters.
/// Use [`CString::from_str`] which will check for interior nulls, or
/// [`CString::from_bytes_with_nul`] for bytes that already include the terminator.
///
/// # Example
///
/// ```
/// use stringly::{CString, String, Utf8};
///
/// let s: String<Utf8> = String::from("hello");
/// let cstring = CString::from_str(&s);
/// assert_eq!(cstring.len(), 5);
/// assert_eq!(cstring.as_bytes_with_nul(), b"hello\0");
/// ```
pub struct CString<E: Encoding> {
    /// The underlying byte vector, including the null terminator.
    bytes: Vec<u8>,
    _marker: PhantomData<E>,
}

impl<E: Encoding> CString<E> {
    /// Creates a new empty `CString`.
    ///
    /// The resulting string contains only the null terminator.
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CString, Utf8};
    ///
    /// let empty = CString::<Utf8>::new();
    /// assert!(empty.is_empty());
    /// assert_eq!(empty.as_bytes_with_nul(), b"\0");
    /// ```
    #[inline]
    pub fn new() -> Self {
        let mut bytes = Vec::with_capacity(E::NULL_LEN);
        bytes.extend(core::iter::repeat(0).take(E::NULL_LEN));
        Self {
            bytes,
            _marker: PhantomData,
        }
    }

    /// Creates a `CString` from a `Str<E>`, appending a null terminator.
    ///
    /// # Panics
    ///
    /// Panics if the string contains an interior null character.
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CString, String, Utf8};
    ///
    /// let s: String<Utf8> = String::from("hello");
    /// let cstring = CString::from_str(&s);
    /// assert_eq!(cstring.as_bytes(), b"hello");
    /// ```
    pub fn from_str(s: &Str<E>) -> Self {
        Self::try_from_str(s).expect("string contains interior null character")
    }

    /// Tries to create a `CString` from a `Str<E>`, appending a null terminator.
    ///
    /// # Errors
    ///
    /// Returns an error if the string contains an interior null character.
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CString, String, Utf8};
    ///
    /// let s: String<Utf8> = String::from("hello");
    /// let cstring = CString::try_from_str(&s).unwrap();
    /// assert_eq!(cstring.as_bytes(), b"hello");
    /// ```
    pub fn try_from_str(s: &Str<E>) -> Result<Self, FromBytesWithNulError> {
        // Check for interior nulls
        for (idx, c) in s.char_indices() {
            if c == '\0' {
                return Err(FromBytesWithNulError::interior_nul(idx));
            }
        }

        let mut bytes = Vec::with_capacity(s.len() + E::NULL_LEN);
        bytes.extend_from_slice(s.as_bytes());
        bytes.extend(core::iter::repeat(0).take(E::NULL_LEN));

        Ok(Self {
            bytes,
            _marker: PhantomData,
        })
    }

    /// Creates a `CString` from a byte vector containing a null terminator.
    ///
    /// The vector must:
    /// - End with the appropriate null terminator for the encoding
    /// - Not contain any interior null characters
    /// - Be valid for the encoding
    ///
    /// # Errors
    ///
    /// Returns an error (with the original bytes) if any of the above conditions
    /// are not met.
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CString, Utf8};
    ///
    /// let cstring = CString::<Utf8>::from_bytes_with_nul(b"hello\0".to_vec()).unwrap();
    /// assert_eq!(cstring.len(), 5);
    /// ```
    pub fn from_bytes_with_nul(bytes: Vec<u8>) -> Result<Self, FromBytesWithNulVecError> {
        // Validate using CStr
        match CStr::<E>::from_bytes_with_nul(&bytes) {
            Ok(_) => Ok(Self {
                bytes,
                _marker: PhantomData,
            }),
            Err(e) => Err(FromBytesWithNulVecError::new(bytes, e)),
        }
    }

    /// Creates a `CString` from a byte vector without checking validity.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - The vector ends with the appropriate null terminator for the encoding
    /// - The vector does not contain interior null characters
    /// - The vector is valid for the encoding
    #[inline]
    pub unsafe fn from_bytes_with_nul_unchecked(bytes: Vec<u8>) -> Self {
        Self {
            bytes,
            _marker: PhantomData,
        }
    }

    /// Creates a `CString` from a byte vector containing a null terminator.
    ///
    /// This is an alias for [`from_bytes_with_nul`] for compatibility with
    /// [`alloc::ffi::CString::from_vec_with_nul`].
    ///
    /// [`from_bytes_with_nul`]: Self::from_bytes_with_nul
    #[inline]
    pub fn from_vec_with_nul(bytes: Vec<u8>) -> Result<Self, FromBytesWithNulVecError> {
        Self::from_bytes_with_nul(bytes)
    }

    /// Creates a `CString` from a byte vector without checking validity.
    ///
    /// This is an alias for [`from_bytes_with_nul_unchecked`] for compatibility
    /// with [`alloc::ffi::CString::from_vec_with_nul_unchecked`].
    ///
    /// # Safety
    ///
    /// See [`from_bytes_with_nul_unchecked`](Self::from_bytes_with_nul_unchecked).
    #[inline]
    pub unsafe fn from_vec_with_nul_unchecked(bytes: Vec<u8>) -> Self {
        unsafe { Self::from_bytes_with_nul_unchecked(bytes) }
    }

    /// Creates a `CString` from a byte vector without interior null checks.
    ///
    /// This method appends the null terminator and assumes no interior nulls.
    /// Unlike [`from_bytes_with_nul_unchecked`], the input should NOT already
    /// contain a null terminator.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - The vector does not contain interior null characters
    /// - The vector is valid for the encoding
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CString, Utf8};
    ///
    /// let cstring = unsafe { CString::<Utf8>::from_vec_unchecked(b"hello".to_vec()) };
    /// assert_eq!(cstring.as_bytes(), b"hello");
    /// assert_eq!(cstring.as_bytes_with_nul(), b"hello\0");
    /// ```
    #[inline]
    pub unsafe fn from_vec_unchecked(mut bytes: Vec<u8>) -> Self {
        bytes.reserve(E::NULL_LEN);
        for _ in 0..E::NULL_LEN {
            bytes.push(0);
        }
        Self {
            bytes,
            _marker: PhantomData,
        }
    }

    /// Consumes this `CString` and returns the underlying byte vector,
    /// excluding the null terminator.
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CString, Utf8};
    ///
    /// let cstring = CString::<Utf8>::from_bytes_with_nul(b"hello\0".to_vec()).unwrap();
    /// let bytes = cstring.into_bytes();
    /// assert_eq!(bytes, b"hello");
    /// ```
    #[inline]
    pub fn into_bytes(mut self) -> Vec<u8> {
        let new_len = self.bytes.len() - E::NULL_LEN;
        self.bytes.truncate(new_len);
        self.bytes
    }

    /// Consumes this `CString` and returns the underlying byte vector,
    /// including the null terminator.
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CString, Utf8};
    ///
    /// let cstring = CString::<Utf8>::from_bytes_with_nul(b"hello\0".to_vec()).unwrap();
    /// let bytes = cstring.into_bytes_with_nul();
    /// assert_eq!(bytes, b"hello\0");
    /// ```
    #[inline]
    pub fn into_bytes_with_nul(self) -> Vec<u8> {
        self.bytes
    }

    /// Returns the inner byte slice, excluding the null terminator.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..self.bytes.len() - E::NULL_LEN]
    }

    /// Returns the inner byte slice, including the null terminator.
    #[inline]
    pub fn as_bytes_with_nul(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns a reference to the underlying `CStr<E>`.
    #[inline]
    pub fn as_c_str(&self) -> &CStr<E> {
        // SAFETY: CString maintains the CStr invariants
        unsafe { CStr::from_bytes_with_nul_unchecked(&self.bytes) }
    }

    /// Returns this C string as a `Str<E>` slice, excluding the null terminator.
    #[inline]
    pub fn as_str(&self) -> &Str<E> {
        self.as_c_str().as_str()
    }

    /// Converts this `CString` into a `String<E>`.
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CString, Utf8};
    ///
    /// let cstring = CString::<Utf8>::from_bytes_with_nul(b"hello\0".to_vec()).unwrap();
    /// let string = cstring.into_string();
    /// assert_eq!(string.len(), 5);
    /// ```
    #[inline]
    pub fn into_string(mut self) -> String<E> {
        let new_len = self.bytes.len() - E::NULL_LEN;
        self.bytes.truncate(new_len);
        // SAFETY: We've already validated the encoding
        unsafe { String::from_bytes_unchecked(self.bytes) }
    }

    /// Converts this `CString` to a `alloc::ffi::CString`.
    ///
    /// For encodings with a 1-byte null terminator (like UTF-8), this is a
    /// zero-copy conversion. For encodings with multi-byte null terminators
    /// (like UTF-16 or UTF-32), the content is transcoded to UTF-8.
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{CString, Utf8};
    ///
    /// let cstring = CString::<Utf8>::from_bytes_with_nul(b"hello\0".to_vec()).unwrap();
    /// let std_cstring: std::ffi::CString = cstring.to_std();
    /// assert_eq!(std_cstring.as_bytes(), b"hello");
    /// ```
    pub fn to_std(self) -> alloc::ffi::CString {
        if E::NULL_LEN == 1 {
            // 1-byte null terminator - zero-copy conversion
            // SAFETY: We have a valid null-terminated string with 1-byte null
            unsafe { alloc::ffi::CString::from_vec_with_nul_unchecked(self.bytes) }
        } else {
            // Multi-byte null terminator - transcode to UTF-8
            let utf8: alloc::string::String = self.chars().collect();
            alloc::ffi::CString::new(utf8).expect("transcoded string contains no interior nulls")
        }
    }

    /// Consumes this `CString` and returns a raw pointer.
    ///
    /// The pointer can be converted back to a `CString` using [`CString::from_raw`].
    ///
    /// The returned pointer must be freed using `CString::from_raw` to avoid a memory leak.
    #[inline]
    pub fn into_raw(self) -> *mut u8 {
        let this = ManuallyDrop::new(self);
        this.bytes.as_ptr() as *mut u8
    }

    /// Recreates a `CString` from a pointer previously obtained via [`CString::into_raw`].
    ///
    /// # Safety
    ///
    /// - `ptr` must have been obtained from `CString::into_raw`
    /// - The `CString` must not have been modified since calling `into_raw`
    /// - This function must only be called once per pointer
    #[inline]
    pub unsafe fn from_raw(ptr: *mut u8) -> Self {
        unsafe {
            // Find the length by scanning for null
            let len = CStr::<E>::strlen(ptr) + E::NULL_LEN;
            let bytes = Vec::from_raw_parts(ptr, len, len);
            Self {
                bytes,
                _marker: PhantomData,
            }
        }
    }

    /// Returns the length of the string in bytes, excluding the null terminator.
    #[inline]
    pub fn len(&self) -> usize {
        self.bytes.len() - E::NULL_LEN
    }

    /// Returns `true` if the string has length 0 (only contains the null terminator).
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns an iterator over the characters of this string.
    #[inline]
    pub fn chars(&self) -> Chars<'_, E> {
        self.as_str().chars()
    }

    /// Converts this `CString` into a boxed `CStr<E>`.
    #[inline]
    pub fn into_boxed_c_str(self) -> Box<CStr<E>> {
        let raw = Box::into_raw(self.bytes.into_boxed_slice()) as *mut CStr<E>;
        // SAFETY: CStr<E> is repr(transparent) over [u8]
        unsafe { Box::from_raw(raw) }
    }
}

// === Trait implementations ===

impl<E: Encoding> Default for CString<E> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<E: Encoding> Clone for CString<E> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            bytes: self.bytes.clone(),
            _marker: PhantomData,
        }
    }
}

impl<E: Encoding> Deref for CString<E> {
    type Target = CStr<E>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_c_str()
    }
}

impl<E: Encoding> Borrow<CStr<E>> for CString<E> {
    #[inline]
    fn borrow(&self) -> &CStr<E> {
        self.as_c_str()
    }
}

impl<E: Encoding> AsRef<CStr<E>> for CString<E> {
    #[inline]
    fn as_ref(&self) -> &CStr<E> {
        self.as_c_str()
    }
}

impl<E: Encoding> AsRef<Str<E>> for CString<E> {
    #[inline]
    fn as_ref(&self) -> &Str<E> {
        self.as_str()
    }
}

impl<E: Encoding> AsRef<[u8]> for CString<E> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<E: Encoding> fmt::Debug for CString<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_c_str(), f)
    }
}

impl<E: Encoding> fmt::Display for CString<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_c_str(), f)
    }
}

impl<E: Encoding> PartialEq for CString<E> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_c_str() == other.as_c_str()
    }
}

impl<E: Encoding> Eq for CString<E> {}

impl<E: Encoding> PartialOrd for CString<E> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<E: Encoding> Ord for CString<E> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_c_str().cmp(other.as_c_str())
    }
}

impl<E: Encoding> Hash for CString<E> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_c_str().hash(state);
    }
}

impl<E: Encoding> From<&Str<E>> for CString<E> {
    /// Creates a `CString` from a `&Str<E>`, appending a null terminator.
    ///
    /// # Panics
    ///
    /// Panics if the string contains an interior null character.
    #[inline]
    fn from(s: &Str<E>) -> Self {
        Self::from_str(s)
    }
}

impl<E: Encoding> From<String<E>> for CString<E> {
    /// Creates a `CString` from a `String<E>`, appending a null terminator.
    ///
    /// # Panics
    ///
    /// Panics if the string contains an interior null character.
    #[inline]
    fn from(s: String<E>) -> Self {
        Self::from_str(&s)
    }
}

impl<E: Encoding> From<&CStr<E>> for CString<E> {
    #[inline]
    fn from(s: &CStr<E>) -> Self {
        Self {
            bytes: s.as_bytes_with_nul().to_vec(),
            _marker: PhantomData,
        }
    }
}

impl<E: Encoding> From<CString<E>> for String<E> {
    #[inline]
    fn from(s: CString<E>) -> Self {
        s.into_string()
    }
}

impl<E: Encoding> From<Box<CStr<E>>> for CString<E> {
    #[inline]
    fn from(s: Box<CStr<E>>) -> Self {
        // Convert Box<CStr<E>> to Box<[u8]> then to Vec<u8>
        let raw = Box::into_raw(s) as *mut [u8];
        let bytes = unsafe { Box::from_raw(raw) }.into_vec();
        Self {
            bytes,
            _marker: PhantomData,
        }
    }
}

impl<'a, E: Encoding> From<&'a CStr<E>> for Cow<'a, CStr<E>> {
    #[inline]
    fn from(s: &'a CStr<E>) -> Self {
        Cow::Borrowed(s)
    }
}

impl<E: Encoding> From<CString<E>> for Cow<'_, CStr<E>> {
    #[inline]
    fn from(s: CString<E>) -> Self {
        Cow::Owned(s)
    }
}

// ToOwned implementation for CStr
impl<E: Encoding> alloc::borrow::ToOwned for CStr<E> {
    type Owned = CString<E>;

    #[inline]
    fn to_owned(&self) -> CString<E> {
        CString::from(self)
    }
}

// Index implementations
impl<E: Encoding> core::ops::Index<core::ops::RangeFull> for CString<E> {
    type Output = CStr<E>;

    #[inline]
    fn index(&self, _: core::ops::RangeFull) -> &Self::Output {
        self.as_c_str()
    }
}
