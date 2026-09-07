//! Cryptographic content: the math, tables, and constants the corpus
//! algorithms consume. Math is content the operations consume — these
//! modules are the math, not new primitives.
//!
//! The six primitives in [`crate::primitives`] are the *what you need
//! to build the algorithm*. The modules here are the *what the
//! algorithm operates on* — the byte strings, finite-field arithmetic,
//! S-boxes, round constants, curve points, and bignum limbs that fill
//! the primitive skeleton.
//!
//! The modules separate byte representation, constants, and transformations:
//!
//! - [`byte_string`] — byte and hex helpers.
//! - [`tables`]      — SHA-256 round constants.

pub mod byte_string;
pub mod keccak;
pub mod tables;
