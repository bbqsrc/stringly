//! Legacy codepage encodings.
//!
//! This module provides support for various legacy character encodings
//! (codepages) commonly used in older systems and file formats.
//!
//! # Available Codepages
//!
//! When the `codepages` feature is enabled, the following encodings are available:
//!
//! - `Iso8859_1` (ISO-8859-1, Latin-1)
//! - `Cp1252` (Windows-1252, Western European)
//!
//! # Example
//!
//! ```ignore
//! use stringly::{String, Str};
//! use stringly::codepages::Cp1252;
//!
//! // Create a string in Windows-1252 encoding
//! let s: String<Cp1252> = "Hello".chars().collect();
//!
//! // Check if a character can be encoded
//! assert!(Cp1252::can_encode('€'));  // Euro sign is in CP1252
//! assert!(!Cp1252::can_encode('中')); // Chinese character is not
//! ```

use alloc::vec;
use alloc::vec::Vec;

// Include the generated codepage implementations
include!(concat!(env!("OUT_DIR"), "/codepages.rs"));
