// Hashes — concrete instantiations of the iterated-
// transformation pattern (SHA-256, SHA-3-256, BLAKE3).
//
// SHA-256 and SHA-3-256 instantiate directly (Merkle-Damgaard and
// sponge respectively); BLAKE3 instantiates tree_fold_of_chunks on
// top of a compression that itself is composition-shaped.

pub mod blake3;
pub mod sha256;
pub mod sha3_256;
