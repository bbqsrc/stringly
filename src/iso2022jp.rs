//! ISO-2022-JP encoding.
//!
//! ISO-2022-JP is a stateful encoding that uses escape sequences to switch between
//! different character sets. It was commonly used for Japanese email.
//!
//! # Structure
//!
//! ISO-2022-JP uses escape sequences to switch between states:
//! - ESC ( B - ASCII (default state)
//! - ESC ( J - JIS X 0201 Roman (almost identical to ASCII)
//! - ESC $ @ - JIS X 0208-1978
//! - ESC $ B - JIS X 0208-1983
//!
//! # Stateful Decoding
//!
//! Because this is a stateful encoding, decoding at an arbitrary offset requires
//! scanning from the beginning of the string to track escape sequences. This makes
//! random access O(n) instead of O(1).

use crate::encoding::Encoding;
use crate::error::EncodingError;

// Include generated tables (JIS X 0208 only - shared with EUC-JP)
include!(concat!(env!("OUT_DIR"), "/jis0208_tables.rs"));

/// ISO-2022-JP encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Iso2022Jp;

/// State of the ISO-2022-JP decoder.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    /// ASCII mode (ESC ( B) - default
    Ascii,
    /// JIS X 0201 Roman mode (ESC ( J)
    Roman,
    /// JIS X 0208 mode (ESC $ @ or ESC $ B)
    Jis0208,
}

impl Encoding for Iso2022Jp {
    const NAME: &'static str = "ISO-2022-JP";
    const IS_FIXED_WIDTH: bool = false;
    const BYTES_PER_CHAR: Option<usize> = None;
    const MAX_CHAR_LEN: usize = 2; // Plus escape sequences

    fn validate(bytes: &[u8]) -> Result<(), EncodingError> {
        let mut state = State::Ascii;
        let mut i = 0;

        while i < bytes.len() {
            if bytes[i] == 0x1B {
                // Escape sequence
                match parse_escape(bytes, i) {
                    Some((new_state, len)) => {
                        state = new_state;
                        i += len;
                    }
                    None => {
                        return Err(EncodingError::new(i, Some(1)));
                    }
                }
            } else {
                match state {
                    State::Ascii | State::Roman => {
                        let b = bytes[i];
                        // ASCII/Roman: 0x21-0x7E (printable) or 0x0A, 0x0D (newlines)
                        if b == 0x0A || b == 0x0D || (0x20..=0x7E).contains(&b) {
                            i += 1;
                        } else {
                            return Err(EncodingError::new(i, Some(1)));
                        }
                    }
                    State::Jis0208 => {
                        if i + 1 >= bytes.len() {
                            return Err(EncodingError::new(i, Some(1)));
                        }
                        let b1 = bytes[i];
                        let b2 = bytes[i + 1];
                        // JIS X 0208: 0x21-0x7E for both bytes
                        if !(0x21..=0x7E).contains(&b1) || !(0x21..=0x7E).contains(&b2) {
                            return Err(EncodingError::new(i, Some(2)));
                        }
                        // Validate the sequence maps to a valid character
                        let pointer = ((b1 - 0x21) as u16) * 94 + (b2 - 0x21) as u16;
                        if jis0208_lookup(pointer).is_none() {
                            return Err(EncodingError::new(i, Some(2)));
                        }
                        i += 2;
                    }
                }
            }
        }
        Ok(())
    }

    fn decode_char_at(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        if offset >= bytes.len() {
            return None;
        }

        // Scan from the beginning to determine the state at offset
        let state = state_at_offset(bytes, offset)?;

        // Check if we're at an escape sequence
        if bytes[offset] == 0x1B {
            return None; // Can't decode an escape sequence as a character
        }

        match state {
            State::Ascii | State::Roman => {
                let b = bytes[offset];
                if b == 0x0A || b == 0x0D || (0x20..=0x7E).contains(&b) {
                    // JIS X 0201 Roman has slight differences (yen sign, overline)
                    // but for simplicity we treat them as ASCII
                    Some((b as char, offset + 1))
                } else {
                    None
                }
            }
            State::Jis0208 => {
                let b1 = *bytes.get(offset)?;
                let b2 = *bytes.get(offset + 1)?;
                if (0x21..=0x7E).contains(&b1) && (0x21..=0x7E).contains(&b2) {
                    let pointer = ((b1 - 0x21) as u16) * 94 + (b2 - 0x21) as u16;
                    let c = jis0208_lookup(pointer)?;
                    Some((c, offset + 2))
                } else {
                    None
                }
            }
        }
    }

    fn encoded_len(c: char) -> usize {
        let cp = c as u32;

        // ASCII (excluding ESC)
        if cp < 0x80 && cp != 0x1B {
            return 1;
        }

        // Check if it's in JIS X 0208
        if jis0208_encode_lookup(c).is_some() {
            return 2;
        }

        // Can't encode
        1
    }

    fn encode_char(c: char, buf: &mut [u8]) -> usize {
        let cp = c as u32;

        // ASCII (excluding ESC)
        if cp < 0x80 && cp != 0x1B {
            buf[0] = cp as u8;
            return 1;
        }

        // JIS X 0208
        if let Some(pointer) = jis0208_encode_lookup(c) {
            let row = pointer / 94;
            let col = pointer % 94;
            buf[0] = (row + 0x21) as u8;
            buf[1] = (col + 0x21) as u8;
            return 2;
        }

        panic!(
            "character '{}' (U+{:04X}) cannot be encoded in ISO-2022-JP",
            c, cp
        );
    }

    fn try_encode_char(c: char, buf: &mut [u8]) -> Option<usize> {
        let cp = c as u32;

        // ASCII (excluding ESC)
        if cp < 0x80 && cp != 0x1B {
            buf[0] = cp as u8;
            return Some(1);
        }

        // JIS X 0208
        if let Some(pointer) = jis0208_encode_lookup(c) {
            let row = pointer / 94;
            let col = pointer % 94;
            buf[0] = (row + 0x21) as u8;
            buf[1] = (col + 0x21) as u8;
            return Some(2);
        }

        None
    }

    fn can_encode(c: char) -> bool {
        let cp = c as u32;

        // ASCII (excluding ESC)
        if cp < 0x80 && cp != 0x1B {
            return true;
        }

        // JIS X 0208
        jis0208_encode_lookup(c).is_some()
    }

    fn is_char_boundary(bytes: &[u8], index: usize) -> bool {
        if index == 0 || index >= bytes.len() {
            return index <= bytes.len();
        }

        // Check if we're in the middle of an escape sequence
        // ESC sequences are 3 bytes: 1B xx xx
        if index >= 1 && bytes[index - 1] == 0x1B {
            return false; // After ESC
        }
        if index >= 2 && bytes[index - 2] == 0x1B {
            return false; // Second byte after ESC
        }

        // Determine state at this position
        if let Some(state) = state_at_offset(bytes, index) {
            match state {
                State::Ascii | State::Roman => true,
                State::Jis0208 => {
                    // In JIS X 0208 mode, check if we're at the second byte
                    // We need to count characters from the last escape sequence
                    // to see if we're on an even or odd byte
                    let mut scan = index;
                    while scan > 0 && bytes[scan - 1] != 0x1B {
                        scan -= 1;
                    }
                    // Skip past the escape sequence
                    if scan >= 3 && bytes[scan - 1] == 0x1B {
                        scan += 2; // Skip the two bytes after ESC
                    }
                    // Count how many bytes since the escape sequence
                    let offset_from_escape = index - scan;
                    offset_from_escape % 2 == 0
                }
            }
        } else {
            false
        }
    }

    fn decode_char_before(bytes: &[u8], offset: usize) -> Option<(char, usize)> {
        if offset == 0 || offset > bytes.len() {
            return None;
        }

        // We need to find the previous character, which requires knowing the state
        // at that position. This is tricky because we don't know where the previous
        // character started.

        // First, check if we're right after an escape sequence
        if offset >= 3 && bytes[offset - 3] == 0x1B {
            // We're right after an escape sequence, go back before it
            return Self::decode_char_before(bytes, offset - 3);
        }

        // Determine state at offset - 1 (where the character might end)
        // We scan from the beginning to find all escape sequences up to offset
        let mut state = State::Ascii;
        let mut i = 0;
        let mut last_char_start = 0;
        let mut last_char_state = State::Ascii;

        while i < offset {
            if bytes[i] == 0x1B {
                if let Some((new_state, len)) = parse_escape(bytes, i) {
                    state = new_state;
                    i += len;
                    continue;
                }
            }

            last_char_start = i;
            last_char_state = state;

            match state {
                State::Ascii | State::Roman => {
                    i += 1;
                }
                State::Jis0208 => {
                    i += 2;
                }
            }
        }

        // If we overshot, we were in the middle of a character
        if i > offset {
            // Recalculate - go back one character
            // This shouldn't happen if offset is a valid boundary
            return None;
        }

        // last_char_start should be the start of the character ending at offset
        if last_char_start >= offset {
            return None;
        }

        // Decode at last_char_start
        match last_char_state {
            State::Ascii | State::Roman => {
                let b = bytes[last_char_start];
                if b == 0x0A || b == 0x0D || (0x20..=0x7E).contains(&b) {
                    Some((b as char, last_char_start))
                } else {
                    None
                }
            }
            State::Jis0208 => {
                if last_char_start + 1 >= offset {
                    return None;
                }
                let b1 = bytes[last_char_start];
                let b2 = bytes[last_char_start + 1];
                if (0x21..=0x7E).contains(&b1) && (0x21..=0x7E).contains(&b2) {
                    let pointer = ((b1 - 0x21) as u16) * 94 + (b2 - 0x21) as u16;
                    let c = jis0208_lookup(pointer)?;
                    Some((c, last_char_start))
                } else {
                    None
                }
            }
        }
    }
}

/// Parse an escape sequence at the given position.
/// Returns the new state and the length of the escape sequence.
fn parse_escape(bytes: &[u8], pos: usize) -> Option<(State, usize)> {
    if bytes.get(pos)? != &0x1B {
        return None;
    }

    let b1 = *bytes.get(pos + 1)?;
    let b2 = *bytes.get(pos + 2)?;

    match (b1, b2) {
        // ESC ( B - ASCII
        (0x28, 0x42) => Some((State::Ascii, 3)),
        // ESC ( J - JIS X 0201 Roman
        (0x28, 0x4A) => Some((State::Roman, 3)),
        // ESC $ @ - JIS X 0208-1978
        (0x24, 0x40) => Some((State::Jis0208, 3)),
        // ESC $ B - JIS X 0208-1983
        (0x24, 0x42) => Some((State::Jis0208, 3)),
        _ => None,
    }
}

/// Determine the decoder state at a given offset by scanning from the beginning.
fn state_at_offset(bytes: &[u8], offset: usize) -> Option<State> {
    let mut state = State::Ascii;
    let mut i = 0;

    while i < offset {
        if i >= bytes.len() {
            break;
        }

        if bytes[i] == 0x1B {
            if let Some((new_state, len)) = parse_escape(bytes, i) {
                state = new_state;
                i += len;
                continue;
            }
        }

        // Skip the character
        match state {
            State::Ascii | State::Roman => {
                i += 1;
            }
            State::Jis0208 => {
                i += 2;
            }
        }
    }

    Some(state)
}

/// Look up a character in the JIS X 0208 decode table.
fn jis0208_lookup(pointer: u16) -> Option<char> {
    JIS0208_DECODE
        .binary_search_by_key(&pointer, |&(p, _)| p)
        .ok()
        .map(|i| JIS0208_DECODE[i].1)
}

/// Look up the pointer for a character in JIS X 0208.
fn jis0208_encode_lookup(c: char) -> Option<u16> {
    JIS0208_ENCODE
        .binary_search_by_key(&c, |&(ch, _)| ch)
        .ok()
        .map(|i| JIS0208_ENCODE[i].1)
}

impl crate::encoding::LimitedEncoding for Iso2022Jp {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ascii() {
        let bytes = b"Hello";
        assert_eq!(Iso2022Jp::decode_char_at(bytes, 0), Some(('H', 1)));
        assert_eq!(Iso2022Jp::decode_char_at(bytes, 1), Some(('e', 2)));
    }

    #[test]
    fn test_escape_sequence() {
        // ESC $ B (switch to JIS X 0208)
        let bytes = &[0x1B, 0x24, 0x42];
        assert!(Iso2022Jp::validate(bytes).is_ok());
        // Can't decode at escape position
        assert_eq!(Iso2022Jp::decode_char_at(bytes, 0), None);
    }

    #[test]
    fn test_jis0208() {
        // "あ" in JIS X 0208 is row 4, col 2 (0-indexed from 0x21)
        // ESC $ B + character + ESC ( B
        let bytes = &[
            0x1B, 0x24, 0x42, // ESC $ B (switch to JIS X 0208)
            0x24, 0x22, // "あ" (hiragana A)
            0x1B, 0x28, 0x42, // ESC ( B (switch back to ASCII)
        ];

        assert!(Iso2022Jp::validate(bytes).is_ok());

        // Decode at position 3 (after escape sequence)
        let decoded = Iso2022Jp::decode_char_at(bytes, 3);
        assert_eq!(decoded, Some(('あ', 5)));
    }

    #[test]
    fn test_validate() {
        // Valid ASCII
        assert!(Iso2022Jp::validate(b"Hello").is_ok());

        // Valid escape sequence
        assert!(Iso2022Jp::validate(&[0x1B, 0x24, 0x42]).is_ok());

        // Invalid: truncated escape
        assert!(Iso2022Jp::validate(&[0x1B, 0x24]).is_err());

        // Invalid: unknown escape
        assert!(Iso2022Jp::validate(&[0x1B, 0x99, 0x99]).is_err());
    }

    #[test]
    fn test_encode_ascii() {
        let mut buf = [0u8; 2];
        assert_eq!(Iso2022Jp::encode_char('A', &mut buf), 1);
        assert_eq!(buf[0], b'A');
    }

    #[test]
    fn test_encode_japanese() {
        // Note: encode_char doesn't include escape sequences,
        // just the raw character bytes
        let mut buf = [0u8; 2];
        let len = Iso2022Jp::encode_char('あ', &mut buf);
        assert_eq!(len, 2);
        assert_eq!(buf[0], 0x24);
        assert_eq!(buf[1], 0x22);
    }

    #[test]
    fn test_mixed_content() {
        // "Aあ" - ASCII 'A' + JIS X 0208 'あ'
        let bytes = &[
            b'A', // ASCII 'A'
            0x1B, 0x24, 0x42, // ESC $ B
            0x24, 0x22, // "あ"
            0x1B, 0x28, 0x42, // ESC ( B
        ];

        assert!(Iso2022Jp::validate(bytes).is_ok());

        // Decode 'A'
        assert_eq!(Iso2022Jp::decode_char_at(bytes, 0), Some(('A', 1)));

        // Decode 'あ' at position 4 (after escape)
        assert_eq!(Iso2022Jp::decode_char_at(bytes, 4), Some(('あ', 6)));
    }
}
