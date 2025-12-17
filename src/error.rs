use core::fmt;

/// An error indicating that a byte slice is not valid for a given encoding.
///
/// Matches the shape of `std::str::Utf8Error`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncodingError {
    valid_up_to: usize,
    error_len: Option<usize>,
}

impl EncodingError {
    /// Creates a new encoding error.
    #[inline]
    pub const fn new(valid_up_to: usize, error_len: Option<usize>) -> Self {
        Self {
            valid_up_to,
            error_len,
        }
    }

    /// Returns the index in the given string up to which valid encoded data was verified.
    ///
    /// It is the maximum index such that `bytes[..index]` is valid.
    #[inline]
    pub const fn valid_up_to(&self) -> usize {
        self.valid_up_to
    }

    /// Provides more information about the failure:
    ///
    /// * `None`: the end of the input was reached unexpectedly.
    /// * `Some(len)`: an unexpected byte was encountered. The length indicates
    ///   how many bytes starting at the index given by `valid_up_to()` are invalid.
    #[inline]
    pub const fn error_len(&self) -> Option<usize> {
        self.error_len
    }
}

impl fmt::Display for EncodingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(error_len) = self.error_len {
            write!(
                f,
                "invalid encoding sequence of {} bytes from index {}",
                error_len, self.valid_up_to
            )
        } else {
            write!(
                f,
                "incomplete encoding sequence from index {}",
                self.valid_up_to
            )
        }
    }
}

impl std::error::Error for EncodingError {}

/// An error returned when conversion from a `Vec<u8>` to `String<E>` fails.
///
/// Matches the shape of `std::string::FromUtf8Error`.
pub struct FromBytesError<E> {
    bytes: Vec<u8>,
    error: EncodingError,
    _marker: core::marker::PhantomData<E>,
}

impl<E> FromBytesError<E> {
    /// Creates a new `FromBytesError`.
    #[inline]
    pub(crate) fn new(bytes: Vec<u8>, error: EncodingError) -> Self {
        Self {
            bytes,
            error,
            _marker: core::marker::PhantomData,
        }
    }

    /// Returns a slice of the bytes that were attempted to be converted.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Consumes this error, returning the bytes that were attempted to be converted.
    #[inline]
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    /// Returns the encoding error that caused the conversion to fail.
    #[inline]
    pub fn encoding_error(&self) -> &EncodingError {
        &self.error
    }
}

impl<E> fmt::Debug for FromBytesError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FromBytesError")
            .field("bytes", &self.bytes)
            .field("error", &self.error)
            .finish()
    }
}

impl<E> fmt::Display for FromBytesError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

impl<E: fmt::Debug> std::error::Error for FromBytesError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}

impl<E> Clone for FromBytesError<E> {
    fn clone(&self) -> Self {
        Self {
            bytes: self.bytes.clone(),
            error: self.error.clone(),
            _marker: core::marker::PhantomData,
        }
    }
}

impl<E> PartialEq for FromBytesError<E> {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes && self.error == other.error
    }
}

impl<E> Eq for FromBytesError<E> {}

/// An error when transcoding to an encoding that cannot represent all characters.
///
/// This error is returned by `TryFrom` implementations when converting between
/// string types and the target encoding cannot represent a character from the source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TranscodeError {
    /// The character that couldn't be encoded.
    pub character: char,
    /// The index (in characters) where the error occurred.
    pub index: usize,
}

impl TranscodeError {
    /// Creates a new transcode error.
    #[inline]
    pub const fn new(character: char, index: usize) -> Self {
        Self { character, index }
    }

    /// Returns the character that couldn't be encoded.
    #[inline]
    pub const fn character(&self) -> char {
        self.character
    }

    /// Returns the character index where the error occurred.
    #[inline]
    pub const fn index(&self) -> usize {
        self.index
    }
}

impl fmt::Display for TranscodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "character '{}' (U+{:04X}) at index {} cannot be encoded in target encoding",
            self.character, self.character as u32, self.index
        )
    }
}

impl std::error::Error for TranscodeError {}
