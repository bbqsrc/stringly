//! String encoding abstraction library.
//!
//! This crate provides generic `String<E>` and `Str<E>` types parameterized by encoding,
//! allowing code to be generic over UTF-8, UTF-16LE/BE, and custom encodings.
//!
//! # Example
//!
//! ```
//! use stringly::{String, Str, Utf8, Utf16Le};
//!
//! // Functions can be generic over encoding
//! fn process<E: stringly::Encoding>(s: &Str<E>) {
//!     for c in s.chars() {
//!         println!("{}", c);
//!     }
//! }
//!
//! // Transcoding via From
//! let utf8: String<Utf8> = String::from("hello");
//! let utf16: String<Utf16Le> = utf8.chars().collect();
//! ```

#![deny(missing_docs)]
#![allow(clippy::new_without_default)]

/// Encoding trait and related types.
pub mod encoding;
/// Error types for encoding operations.
pub mod error;
/// Iterator types for strings.
pub mod iter;
/// Pattern matching traits for string searching.
pub mod pattern;
/// The `Str<E>` borrowed string slice type.
pub mod str;
/// The `String<E>` owned string type.
pub mod string;
/// UTF-8 encoding implementation.
pub mod utf8;

/// UTF-16 big-endian encoding implementation.
#[cfg(feature = "utf16")]
pub mod utf16be;
/// UTF-16 little-endian encoding implementation.
#[cfg(feature = "utf16")]
pub mod utf16le;

/// UTF-32 big-endian encoding implementation.
#[cfg(feature = "utf32")]
pub mod utf32be;
/// UTF-32 little-endian encoding implementation.
#[cfg(feature = "utf32")]
pub mod utf32le;

/// GB18030 encoding implementation.
#[cfg(feature = "gb18030")]
pub mod gb18030;

/// CESU-8 encoding implementation.
#[cfg(feature = "cesu8")]
pub mod cesu8;

/// UTF-7 encoding implementations (standard and IMAP).
#[cfg(feature = "utf7")]
pub mod utf7;

/// UTF-EBCDIC encoding implementation.
#[cfg(feature = "utf-ebcdic")]
pub mod utf_ebcdic;

/// EUC-JP encoding implementation.
#[cfg(feature = "euc-jp")]
pub mod eucjp;
/// ISO-2022-JP encoding implementation.
#[cfg(feature = "iso-2022-jp")]
pub mod iso2022jp;

/// Legacy codepage encoding implementations.
#[cfg(any(
    feature = "codepages-iso8859",
    feature = "codepages-windows",
    feature = "codepages-dos",
    feature = "codepages-apple",
    feature = "codepages-misc",
))]
pub mod codepages;

/// Runtime encoding registry for dynamic encoding selection.
#[cfg(feature = "registry")]
pub mod registry;

// Re-export main types
pub use encoding::{Encoding, LimitedEncoding, UniversalEncoding};
pub use error::{EncodingError, FromBytesError, TranscodeError};
pub use iter::{
    Bytes, CharIndices, Chars, Drain, EscapeDebug, EscapeDefault, EscapeUnicode, Lines,
    MatchIndices, Matches, RMatchIndices, RMatches, RSplit, RSplitN, RSplitTerminator, Split,
    SplitAsciiWhitespace, SplitInclusive, SplitN, SplitTerminator, SplitWhitespace,
};
pub use pattern::{
    CharArraySearcher, CharPredicateSearcher, CharSearcher, CharSliceSearcher, DoubleEndedSearcher,
    Pattern, ReverseSearcher, SearchStep, Searcher, StrSearcher,
};
pub use str::Str;
pub use string::String;

// Always available
pub use utf8::{StdStrSearcher, Utf8};

// Feature-gated re-exports
#[cfg(feature = "cesu8")]
pub use cesu8::Cesu8;
#[cfg(feature = "euc-jp")]
pub use eucjp::EucJp;
#[cfg(feature = "gb18030")]
pub use gb18030::Gb18030;
#[cfg(feature = "iso-2022-jp")]
pub use iso2022jp::Iso2022Jp;
#[cfg(feature = "utf-ebcdic")]
pub use utf_ebcdic::UtfEbcdic;
#[cfg(feature = "utf7")]
pub use utf7::{Utf7, Utf7Imap};
#[cfg(feature = "utf16")]
pub use utf16be::Utf16Be;
#[cfg(feature = "utf16")]
pub use utf16le::Utf16Le;
#[cfg(feature = "utf32")]
pub use utf32be::Utf32Be;
#[cfg(feature = "utf32")]
pub use utf32le::Utf32Le;

/// A borrowed UTF-8 string slice.
pub type Utf8Str = Str<Utf8>;
/// An owned UTF-8 string.
pub type Utf8String = String<Utf8>;

/// A borrowed UTF-16 little-endian string slice.
#[cfg(feature = "utf16")]
pub type Utf16LeStr = Str<Utf16Le>;
/// An owned UTF-16 little-endian string.
#[cfg(feature = "utf16")]
pub type Utf16LeString = String<Utf16Le>;
/// A borrowed UTF-16 big-endian string slice.
#[cfg(feature = "utf16")]
pub type Utf16BeStr = Str<Utf16Be>;
/// An owned UTF-16 big-endian string.
#[cfg(feature = "utf16")]
pub type Utf16BeString = String<Utf16Be>;
/// A borrowed UTF-32 little-endian string slice.
#[cfg(feature = "utf32")]
pub type Utf32LeStr = Str<Utf32Le>;
/// An owned UTF-32 little-endian string.
#[cfg(feature = "utf32")]
pub type Utf32LeString = String<Utf32Le>;
/// A borrowed UTF-32 big-endian string slice.
#[cfg(feature = "utf32")]
pub type Utf32BeStr = Str<Utf32Be>;
/// An owned UTF-32 big-endian string.
#[cfg(feature = "utf32")]
pub type Utf32BeString = String<Utf32Be>;
/// A borrowed GB18030 string slice.
#[cfg(feature = "gb18030")]
pub type Gb18030Str = Str<Gb18030>;
/// An owned GB18030 string.
#[cfg(feature = "gb18030")]
pub type Gb18030String = String<Gb18030>;
/// A borrowed EUC-JP string slice.
#[cfg(feature = "euc-jp")]
pub type EucJpStr = Str<EucJp>;
/// An owned EUC-JP string.
#[cfg(feature = "euc-jp")]
pub type EucJpString = String<EucJp>;
/// A borrowed ISO-2022-JP string slice.
#[cfg(feature = "iso-2022-jp")]
pub type Iso2022JpStr = Str<Iso2022Jp>;
/// An owned ISO-2022-JP string.
#[cfg(feature = "iso-2022-jp")]
pub type Iso2022JpString = String<Iso2022Jp>;
/// A borrowed CESU-8 string slice.
#[cfg(feature = "cesu8")]
pub type Cesu8Str = Str<Cesu8>;
/// An owned CESU-8 string.
#[cfg(feature = "cesu8")]
pub type Cesu8String = String<Cesu8>;
/// A borrowed UTF-7 string slice.
#[cfg(feature = "utf7")]
pub type Utf7Str = Str<Utf7>;
/// An owned UTF-7 string.
#[cfg(feature = "utf7")]
pub type Utf7String = String<Utf7>;
/// A borrowed UTF-7 IMAP string slice.
#[cfg(feature = "utf7")]
pub type Utf7ImapStr = Str<Utf7Imap>;
/// An owned UTF-7 IMAP string.
#[cfg(feature = "utf7")]
pub type Utf7ImapString = String<Utf7Imap>;
/// A borrowed UTF-EBCDIC string slice.
#[cfg(feature = "utf-ebcdic")]
pub type UtfEbcdicStr = Str<UtfEbcdic>;
/// An owned UTF-EBCDIC string.
#[cfg(feature = "utf-ebcdic")]
pub type UtfEbcdicString = String<UtfEbcdic>;

// =============================================================================
// Cross-encoding conversions
// =============================================================================

/// Macro to generate `From` implementations for universal encoding conversions.
///
/// Universal encodings can represent all Unicode code points, so conversion
/// between them is infallible.
macro_rules! impl_universal_from {
    ($from:ty => $($to:ty),+ $(,)?) => {
        $(
            impl From<&Str<$from>> for String<$to> {
                fn from(s: &Str<$from>) -> Self {
                    s.chars().collect()
                }
            }

            impl From<String<$from>> for String<$to> {
                fn from(s: String<$from>) -> Self {
                    s.chars().collect()
                }
            }
        )+
    };
}

// UTF-8 → other universal encodings
#[cfg(feature = "utf16")]
impl_universal_from!(Utf8 => Utf16Le, Utf16Be);
#[cfg(feature = "utf32")]
impl_universal_from!(Utf8 => Utf32Le, Utf32Be);
#[cfg(feature = "gb18030")]
impl_universal_from!(Utf8 => Gb18030);

// UTF-16LE → other universal encodings
#[cfg(feature = "utf16")]
impl_universal_from!(Utf16Le => Utf8, Utf16Be);
#[cfg(all(feature = "utf16", feature = "utf32"))]
impl_universal_from!(Utf16Le => Utf32Le, Utf32Be);
#[cfg(all(feature = "utf16", feature = "gb18030"))]
impl_universal_from!(Utf16Le => Gb18030);

// UTF-16BE → other universal encodings
#[cfg(feature = "utf16")]
impl_universal_from!(Utf16Be => Utf8, Utf16Le);
#[cfg(all(feature = "utf16", feature = "utf32"))]
impl_universal_from!(Utf16Be => Utf32Le, Utf32Be);
#[cfg(all(feature = "utf16", feature = "gb18030"))]
impl_universal_from!(Utf16Be => Gb18030);

// UTF-32LE → other universal encodings
#[cfg(feature = "utf32")]
impl_universal_from!(Utf32Le => Utf8, Utf32Be);
#[cfg(all(feature = "utf32", feature = "utf16"))]
impl_universal_from!(Utf32Le => Utf16Le, Utf16Be);
#[cfg(all(feature = "utf32", feature = "gb18030"))]
impl_universal_from!(Utf32Le => Gb18030);

// UTF-32BE → other universal encodings
#[cfg(feature = "utf32")]
impl_universal_from!(Utf32Be => Utf8, Utf32Le);
#[cfg(all(feature = "utf32", feature = "utf16"))]
impl_universal_from!(Utf32Be => Utf16Le, Utf16Be);
#[cfg(all(feature = "utf32", feature = "gb18030"))]
impl_universal_from!(Utf32Be => Gb18030);

// GB18030 → other universal encodings
#[cfg(feature = "gb18030")]
impl_universal_from!(Gb18030 => Utf8);
#[cfg(all(feature = "gb18030", feature = "utf16"))]
impl_universal_from!(Gb18030 => Utf16Le, Utf16Be);
#[cfg(all(feature = "gb18030", feature = "utf32"))]
impl_universal_from!(Gb18030 => Utf32Le, Utf32Be);

// CESU-8 → other universal encodings
#[cfg(feature = "cesu8")]
impl_universal_from!(Cesu8 => Utf8);
#[cfg(all(feature = "cesu8", feature = "utf16"))]
impl_universal_from!(Cesu8 => Utf16Le, Utf16Be);
#[cfg(all(feature = "cesu8", feature = "utf32"))]
impl_universal_from!(Cesu8 => Utf32Le, Utf32Be);
#[cfg(all(feature = "cesu8", feature = "gb18030"))]
impl_universal_from!(Cesu8 => Gb18030);

// UTF-7 → other universal encodings
#[cfg(feature = "utf7")]
impl_universal_from!(Utf7 => Utf8);
#[cfg(all(feature = "utf7", feature = "utf16"))]
impl_universal_from!(Utf7 => Utf16Le, Utf16Be);
#[cfg(all(feature = "utf7", feature = "utf32"))]
impl_universal_from!(Utf7 => Utf32Le, Utf32Be);
#[cfg(all(feature = "utf7", feature = "gb18030"))]
impl_universal_from!(Utf7 => Gb18030);
#[cfg(all(feature = "utf7", feature = "cesu8"))]
impl_universal_from!(Utf7 => Cesu8);

// UTF-7-IMAP → other universal encodings
#[cfg(feature = "utf7")]
impl_universal_from!(Utf7Imap => Utf8, Utf7);
#[cfg(all(feature = "utf7", feature = "utf16"))]
impl_universal_from!(Utf7Imap => Utf16Le, Utf16Be);
#[cfg(all(feature = "utf7", feature = "utf32"))]
impl_universal_from!(Utf7Imap => Utf32Le, Utf32Be);
#[cfg(all(feature = "utf7", feature = "gb18030"))]
impl_universal_from!(Utf7Imap => Gb18030);
#[cfg(all(feature = "utf7", feature = "cesu8"))]
impl_universal_from!(Utf7Imap => Cesu8);

// UTF-EBCDIC → other universal encodings
#[cfg(feature = "utf-ebcdic")]
impl_universal_from!(UtfEbcdic => Utf8);
#[cfg(all(feature = "utf-ebcdic", feature = "utf16"))]
impl_universal_from!(UtfEbcdic => Utf16Le, Utf16Be);
#[cfg(all(feature = "utf-ebcdic", feature = "utf32"))]
impl_universal_from!(UtfEbcdic => Utf32Le, Utf32Be);
#[cfg(all(feature = "utf-ebcdic", feature = "gb18030"))]
impl_universal_from!(UtfEbcdic => Gb18030);
#[cfg(all(feature = "utf-ebcdic", feature = "cesu8"))]
impl_universal_from!(UtfEbcdic => Cesu8);
#[cfg(all(feature = "utf-ebcdic", feature = "utf7"))]
impl_universal_from!(UtfEbcdic => Utf7, Utf7Imap);

// UTF-8 → new universal encodings
#[cfg(feature = "cesu8")]
impl_universal_from!(Utf8 => Cesu8);
#[cfg(feature = "utf7")]
impl_universal_from!(Utf8 => Utf7, Utf7Imap);
#[cfg(feature = "utf-ebcdic")]
impl_universal_from!(Utf8 => UtfEbcdic);

// UTF-16LE → new universal encodings
#[cfg(all(feature = "utf16", feature = "cesu8"))]
impl_universal_from!(Utf16Le => Cesu8);
#[cfg(all(feature = "utf16", feature = "utf7"))]
impl_universal_from!(Utf16Le => Utf7, Utf7Imap);
#[cfg(all(feature = "utf16", feature = "utf-ebcdic"))]
impl_universal_from!(Utf16Le => UtfEbcdic);

// UTF-16BE → new universal encodings
#[cfg(all(feature = "utf16", feature = "cesu8"))]
impl_universal_from!(Utf16Be => Cesu8);
#[cfg(all(feature = "utf16", feature = "utf7"))]
impl_universal_from!(Utf16Be => Utf7, Utf7Imap);
#[cfg(all(feature = "utf16", feature = "utf-ebcdic"))]
impl_universal_from!(Utf16Be => UtfEbcdic);

// UTF-32LE → new universal encodings
#[cfg(all(feature = "utf32", feature = "cesu8"))]
impl_universal_from!(Utf32Le => Cesu8);
#[cfg(all(feature = "utf32", feature = "utf7"))]
impl_universal_from!(Utf32Le => Utf7, Utf7Imap);
#[cfg(all(feature = "utf32", feature = "utf-ebcdic"))]
impl_universal_from!(Utf32Le => UtfEbcdic);

// UTF-32BE → new universal encodings
#[cfg(all(feature = "utf32", feature = "cesu8"))]
impl_universal_from!(Utf32Be => Cesu8);
#[cfg(all(feature = "utf32", feature = "utf7"))]
impl_universal_from!(Utf32Be => Utf7, Utf7Imap);
#[cfg(all(feature = "utf32", feature = "utf-ebcdic"))]
impl_universal_from!(Utf32Be => UtfEbcdic);

// GB18030 → new universal encodings
#[cfg(all(feature = "gb18030", feature = "cesu8"))]
impl_universal_from!(Gb18030 => Cesu8);
#[cfg(all(feature = "gb18030", feature = "utf7"))]
impl_universal_from!(Gb18030 => Utf7, Utf7Imap);
#[cfg(all(feature = "gb18030", feature = "utf-ebcdic"))]
impl_universal_from!(Gb18030 => UtfEbcdic);

// =============================================================================
// Fallible encoding conversions via method
// =============================================================================

impl<E: Encoding> Str<E> {
    /// Attempts to transcode this string to a different encoding.
    ///
    /// Returns `Ok` if all characters can be represented in the target encoding.
    /// Returns `Err` with the first character that cannot be encoded.
    ///
    /// # Example
    ///
    /// ```
    /// use stringly::{String, Str, Utf8};
    /// # #[cfg(feature = "codepages-windows")]
    /// # {
    /// use stringly::codepages::Cp1252;
    ///
    /// let utf8: String<Utf8> = String::from("hello");
    /// let cp1252: String<Cp1252> = utf8.try_transcode().unwrap();
    ///
    /// let utf8_cjk: String<Utf8> = String::from("hello 世界");
    /// assert!(utf8_cjk.try_transcode::<Cp1252>().is_err());
    /// # }
    /// ```
    pub fn try_transcode<F: Encoding>(&self) -> Result<String<F>, TranscodeError> {
        let mut result = String::new();
        for (i, c) in self.chars().enumerate() {
            if !F::can_encode(c) {
                return Err(TranscodeError::new(c, i));
            }
            result.push(c);
        }
        Ok(result)
    }
}

impl<E: Encoding> String<E> {
    /// Attempts to transcode this string to a different encoding.
    ///
    /// Returns `Ok` if all characters can be represented in the target encoding.
    /// Returns `Err` with the first character that cannot be encoded.
    ///
    /// See [`Str::try_transcode`] for more details.
    pub fn try_transcode<F: Encoding>(&self) -> Result<String<F>, TranscodeError> {
        (**self).try_transcode()
    }
}
