//! Output-equivalence relations
//! used by the executable comparison.
//!
//! Cryptographic outputs are deterministic byte strings; the comparison
//! relation is byte-for-byte equality. The four relations the
//! Algorithms harness uses (`Exact`, `MultisetInt`, `SetOfIntLists`,
//! `BoolEq`) collapse to `Exact` here — multiset relaxations would mask
//! cryptographic faults.
//!
//! Structured outputs (AEAD ciphertext + tag, signatures, key
//! agreement) are represented as `Value::List` of `Value::Bytes` and
//! compared element-wise under `Exact` — every element must be
//! byte-exact.

use crate::value::Value;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Equiv {
    /// Byte-exact equality. The only relation for the cryptographic
    /// corpus: every algorithm produces a deterministic output and the
    /// reference (a test vector or an independent oracle) is the
    /// authoritative ground truth.
    Exact,
    /// Boolean answer (verification predicates). For round-trip tests:
    /// `verify(public_key, signature, message)` returns a Bool.
    BoolEq,
}

/// True iff `a` and `b` are equivalent under `rel`.
///
/// For `Exact`, this is `PartialEq`. Note that `Value::Bytes` and
/// `Value::Str` are *not* equal under direct `==` even when the Str
/// encodes the same hex — so the harness canonicalizes wire-form `Str`s
/// to `Bytes` before comparing.
pub fn equiv(a: &Value, b: &Value, rel: Equiv) -> bool {
    match rel {
        Equiv::Exact => canon_bytes(a) == canon_bytes(b),
        Equiv::BoolEq => a == b,
    }
}

/// Walk a `Value` and convert every `Str` that decodes as hex into a
/// `Bytes` — the canonical form for byte-typed cryptographic outputs.
/// Strings that don't decode as hex (rare in this corpus, but possible
/// for diagnostic outputs) are left unchanged.
fn canon_bytes(v: &Value) -> Value {
    match v {
        Value::Str(s) => match crate::value::hex_decode(s) {
            Some(b) => Value::Bytes(b),
            None => Value::Str(s.clone()),
        },
        Value::List(l) => Value::List(l.iter().map(canon_bytes).collect()),
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn byte_exact_matches() {
        let a = Value::Bytes(vec![1, 2, 3]);
        let b = Value::Bytes(vec![1, 2, 3]);
        assert!(equiv(&a, &b, Equiv::Exact));
    }
    #[test]
    fn byte_exact_distinguishes_one_bit() {
        let a = Value::Bytes(vec![1, 2, 3]);
        let b = Value::Bytes(vec![1, 2, 4]);
        assert!(!equiv(&a, &b, Equiv::Exact));
    }
    #[test]
    fn wire_form_str_compares_as_bytes() {
        let direct = Value::Bytes(vec![0xDE, 0xAD]);
        let after_wire = Value::Str("dead".into());
        assert!(equiv(&direct, &after_wire, Equiv::Exact));
    }
    #[test]
    fn aead_output_compares_element_wise() {
        let a = Value::List(vec![
            Value::Bytes(vec![1, 2, 3]),
            Value::Bytes(vec![10, 20]),
        ]);
        let b = Value::List(vec![
            Value::Bytes(vec![1, 2, 3]),
            Value::Bytes(vec![10, 20]),
        ]);
        assert!(equiv(&a, &b, Equiv::Exact));
    }
}
