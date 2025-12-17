# stringly

A Rust library providing generic string types parameterized by encoding.

## Overview

`stringly` provides `String<E>` and `Str<E>` types that work like `std`'s `String` and `str`, but are generic over their encoding. This allows you to:

- Write encoding-agnostic code that works with UTF-8, UTF-16, UTF-32, and legacy encodings
- Safely transcode between encodings
- Use the same API you already know from `std`

## Features

- **Generic string types**: `String<E>` (owned) and `Str<E>` (borrowed) parameterized by encoding
- **Full `std` API compatibility**: The same methods as `std::string::String` and `str`
- **Pattern matching**: Generic `Pattern` trait for searching, splitting, and matching
- **Transcoding**: Convert between any encodings via `chars()` iterators
- **Feature-gated encodings**: Enable only the encodings you need

## Supported Encodings

CESU-8, GB18030, UTF-16BE, UTF-16LE, UTF-32BE, UTF-32LE, UTF-7, UTF-7-IMAP, UTF-8, UTF-EBCDIC, ATARIST, Big5, CP037, CP1006, CP1026, CP424, CP437, CP500, CP737, CP775, CP850, CP852, CP855, CP856, CP857, CP860, CP861, CP862, CP863, CP864, CP865, CP866, CP869, CP875, EUC-JP, EUC-KR, ISO-2022-JP, ISO-8859-1, ISO-8859-10, ISO-8859-11, ISO-8859-13, ISO-8859-14, ISO-8859-15, ISO-8859-16, ISO-8859-2, ISO-8859-3, ISO-8859-4, ISO-8859-5, ISO-8859-6, ISO-8859-7, ISO-8859-8, ISO-8859-9, KOI8-R, KOI8-U, KZ1048, MacArabic, MacCeltic, MacCenteuro, MacChinsimp, MacChintrad, MacCroatian, MacCyrillic, MacDevanaga, MacDingbats, MacFarsi, MacGaelic, MacGreek, MacGujarati, MacGurmukhi, MacHebrew, MacIceland, MacInuit, MacJapanese, MacKeyboard, MacKorean, MacRoman, MacRomanian, MacSymbol, MacThai, MacTurkish, Shift_JIS, Windows-1250, Windows-1251, Windows-1252, Windows-1253, Windows-1254, Windows-1255, Windows-1256, Windows-1257, Windows-1258, Windows-874, Windows-932, Windows-936, Windows-949, Windows-950

## Usage

Add to your `Cargo.toml`:

```toml
[dependencies]
stringly = "0.0.0"

# Enable specific encodings
[features]
default = ["stringly/unicode"]  # UTF-16, UTF-32, GB18030, UTF-7, CESU-8, UTF-EBCDIC
```

### Basic Example

```rust
use stringly::{String, Utf8};

// Create a UTF-8 string - same API as std
let s: String<Utf8> = String::from("Hello, world!");
assert!(s.starts_with("Hello"));
```

### Encoding-Generic Functions

```rust
use stringly::{Str, Encoding};

// Write functions that work with any encoding
fn word_count<E: Encoding>(s: &Str<E>) -> usize {
    s.split_whitespace().count()
}
```

### Transcoding

```rust
use stringly::{String, Utf8, Utf16Le, Iso8859_1};

// Universal encodings can convert infallibly via From
let utf8: String<Utf8> = String::from("Hello");
let utf16: String<Utf16Le> = String::from(utf8);

// Limited encodings may fail if characters aren't representable
let utf8: String<Utf8> = String::from("Hello");
let latin1: Option<String<Iso8859_1>> = utf8.try_transcode();
```

## Feature Flags

| Feature | Description |
|---------|-------------|
| `unicode` | **Default.** Enables `utf16`, `utf32`, `gb18030`, `utf7`, `cesu8`, `utf-ebcdic` |
| `utf16` | UTF-16 LE/BE |
| `utf32` | UTF-32 LE/BE |
| `gb18030` | GB18030 (Chinese national standard) |
| `utf7` | UTF-7 and UTF-7 IMAP |
| `cesu8` | CESU-8 (compatibility encoding for UTF-16) |
| `utf-ebcdic` | UTF-EBCDIC (Unicode on EBCDIC systems) |
| `codepages` | All legacy codepages |
| `codepages-iso8859` | ISO-8859-* family |
| `codepages-windows` | Windows-* codepages |
| `codepages-dos` | DOS codepages (CP437, etc.) |
| `codepages-apple` | Apple codepages |
| `codepages-misc` | Miscellaneous codepages |
| `codepages-cjk` | Enables `euc-jp`, `iso-2022-jp`, `shift-jis`, `euc-kr`, `big5` |
| `euc-jp` | EUC-JP |
| `iso-2022-jp` | ISO-2022-JP (stateful) |
| `shift-jis` | Shift_JIS |
| `euc-kr` | EUC-KR |
| `big5` | Big5 |
| `registry` | Runtime encoding registry for CLI tools |

## Encoding Traits

The library defines three levels of encoding capability:

- **`Encoding`**: Base trait for all encodings. Provides character iteration, validation, and basic operations.
- **`LimitedEncoding`**: Encodings that can represent a subset of Unicode (e.g., ISO-8859-1).
- **`UniversalEncoding`**: Encodings that can represent all of Unicode (UTF-8, UTF-16, UTF-32, GB18030, UTF-7, CESU-8, UTF-EBCDIC).

## License

Licensed under either of Apache License, Version 2.0 or MIT license at your option.
