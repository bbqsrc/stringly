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

| Encoding | Feature Flag | Notes |
|----------|-------------|-------|
| UTF-8 | *(always available)* | Default encoding |
| UTF-16 LE/BE | `utf16` | Little/big endian |
| UTF-32 LE/BE | `utf32` | Little/big endian |
| GB18030 | `gb18030` | Chinese national standard |
| UTF-7 | `utf7` | 7-bit safe encoding (RFC 2152) |
| UTF-7 IMAP | `utf7` | Modified UTF-7 for IMAP mailbox names (RFC 3501) |
| CESU-8 | `cesu8` | Compatibility encoding for UTF-16 |
| UTF-EBCDIC | `utf-ebcdic` | Unicode on EBCDIC systems |
| EUC-JP | `euc-jp` | Japanese |
| ISO-2022-JP | `iso-2022-jp` | Japanese (stateful) |
| ISO-8859-* | `codepages-iso8859` | Western European, etc. |
| Windows-* | `codepages-windows` | Windows codepages |
| DOS codepages | `codepages-dos` | CP437, etc. |

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
| `codepages-japanese` | Enables `euc-jp`, `iso-2022-jp` |
| `euc-jp` | EUC-JP |
| `iso-2022-jp` | ISO-2022-JP (stateful) |
| `registry` | Runtime encoding registry for CLI tools |

## Encoding Traits

The library defines three levels of encoding capability:

- **`Encoding`**: Base trait for all encodings. Provides character iteration, validation, and basic operations.
- **`LimitedEncoding`**: Encodings that can represent a subset of Unicode (e.g., ISO-8859-1).
- **`UniversalEncoding`**: Encodings that can represent all of Unicode (UTF-8, UTF-16, UTF-32, GB18030, UTF-7, CESU-8, UTF-EBCDIC).

## License

Licensed under either of Apache License, Version 2.0 or MIT license at your option.
