#![allow(dead_code)]

//! Shared utilities for trace_equivalence harnesses.
//!
//! Each harness encodes a published operational semantics as a Rust
//! trace generator and asserts step-for-step equivalence against the
//! reproduction's trace on a small representative scenario. This
//! module provides the boilerplate.

/// A canonical-trace assertion: `canonical == reproduction`.
/// Used by harnesses that compare ordered sequences of events.
pub fn assert_canonical_eq<T: PartialEq + std::fmt::Debug>(
    framework: &str,
    canonical: &[T],
    reproduction: &[T],
) {
    assert_eq!(
        canonical, reproduction,
        "{}: canonical trace {:?} differs from reproduction trace {:?}",
        framework, canonical, reproduction
    );
    eprintln!(
        "PASS: {} canonical trace = reproduction trace, {} events",
        framework,
        canonical.len()
    );
}

/// A canonical-property assertion: `predicate(reproduction)` must hold.
/// Used by harnesses where the canonical semantics describes a
/// structural property rather than a literal trace.
pub fn assert_property<T: std::fmt::Debug>(
    framework: &str,
    property_name: &str,
    reproduction: &T,
    predicate: impl Fn(&T) -> bool,
) {
    assert!(
        predicate(reproduction),
        "{}: reproduction {:?} violates property {}",
        framework,
        reproduction,
        property_name
    );
    eprintln!(
        "PASS: {} reproduction satisfies {} (per published semantics)",
        framework, property_name
    );
}

/// Cite the paper providing the operational semantics.
pub fn cited(framework: &str, source: &str) {
    eprintln!(
        "trace-equivalence: {} against published semantics ({})",
        framework, source
    );
}
