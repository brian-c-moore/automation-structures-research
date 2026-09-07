//! Byte-string helpers shared across compositions.
//!
//! Hex parsing/printing lives in [`crate::value`] (it's intrinsic to
//! the wire format). This module covers the byte-level operations
//! every cryptographic algorithm needs:
//!
//! - `be_u32` / `be_u32_array`: big-endian word loads (SHA-2 family,
//!   HMAC, HKDF inputs).
//! - `be_u32_to_bytes`: big-endian word stores (SHA-2 output).
//! - `xor_into`: per-byte XOR (a [`Reduction`](crate::primitives::Reduction)
//!   over byte streams).
//! - `pad_md`: Merkle-Damgård padding (length-suffix scheme used by
//!   SHA-2 and MD5; SHA-3 uses a different padding via its sponge
//!   construction).

/// Read a big-endian 32-bit word from `bytes[offset..offset+4]`.
pub fn be_u32(bytes: &[u8], offset: usize) -> u32 {
    u32::from_be_bytes([
        bytes[offset],
        bytes[offset + 1],
        bytes[offset + 2],
        bytes[offset + 3],
    ])
}

/// Write a 32-bit word in big-endian byte order to a 4-byte buffer.
pub fn be_u32_to_bytes(w: u32) -> [u8; 4] {
    w.to_be_bytes()
}

/// Read a little-endian 32-bit word from `bytes[offset..offset+4]`.
/// Used by ChaCha20 (RFC 8439) and BLAKE3.
pub fn le_u32(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes([
        bytes[offset],
        bytes[offset + 1],
        bytes[offset + 2],
        bytes[offset + 3],
    ])
}

/// Write a 32-bit word in little-endian byte order to a 4-byte buffer.
pub fn le_u32_to_bytes(w: u32) -> [u8; 4] {
    w.to_le_bytes()
}

/// Read N consecutive big-endian 32-bit words.
pub fn be_u32_array<const N: usize>(bytes: &[u8], offset: usize) -> [u32; N] {
    let mut out = [0u32; N];
    for (i, slot) in out.iter_mut().enumerate() {
        *slot = be_u32(bytes, offset + i * 4);
    }
    out
}

/// In-place per-byte XOR: `dst[i] ^= src[i]` for i in 0..src.len().
/// `dst.len()` must be >= `src.len()`.
pub fn xor_into(dst: &mut [u8], src: &[u8]) {
    for (d, s) in dst.iter_mut().zip(src.iter()) {
        *d ^= *s;
    }
}

/// Merkle-Damgård padding (RFC 6234 §4.1 / FIPS 180-4 §5.1.1): append
/// 0x80, then 0x00 bytes, then a 64-bit big-endian length suffix
/// (length in bits) so the total length is a multiple of `block_size`.
/// Used by SHA-256 and HMAC-SHA-256.
pub fn pad_md(msg: &[u8], block_size: usize) -> Vec<u8> {
    let bit_len = (msg.len() as u64).wrapping_mul(8);
    let mut padded = Vec::with_capacity(msg.len() + block_size);
    padded.extend_from_slice(msg);
    padded.push(0x80);
    // Pad with zeros until 8 bytes shy of a block boundary.
    while padded.len() % block_size != block_size - 8 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());
    debug_assert_eq!(padded.len() % block_size, 0);
    padded
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn be_u32_load_store_roundtrip() {
        let bytes = [0x12, 0x34, 0x56, 0x78];
        let w = be_u32(&bytes, 0);
        assert_eq!(w, 0x12345678);
        assert_eq!(be_u32_to_bytes(w), bytes);
    }
    #[test]
    fn xor_into_is_pointwise() {
        let mut dst = [0xFFu8; 4];
        xor_into(&mut dst, &[0x0F, 0xF0, 0xAA, 0x55]);
        assert_eq!(dst, [0xF0, 0x0F, 0x55, 0xAA]);
    }
    #[test]
    fn pad_md_block_aligned() {
        // "abc" with SHA-256's 64-byte block: pad to one block.
        let p = pad_md(b"abc", 64);
        assert_eq!(p.len(), 64);
        assert_eq!(p[0..3], *b"abc");
        assert_eq!(p[3], 0x80);
        // Last 8 bytes are the 24-bit-length (3*8 = 24) in big-endian.
        assert_eq!(&p[56..64], &24u64.to_be_bytes());
    }
}
