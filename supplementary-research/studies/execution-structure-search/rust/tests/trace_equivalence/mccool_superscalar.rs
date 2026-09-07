//! trace-equivalence harness for McCool_SuperscalarSequence.
//! Semantics source: McCool, Robison, Reinders (2012), Superscalar Sequence
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_superscalar`,
//! which runs the pattern through real `BoundedQueue` operations
//! exposed by `execution_modalities::primitives`. The assertion is
//! that the kernel correctly implements the pattern: a divergence
//! between canonical and reproduction is a falsification of the
//! configuration.

#[path = "pattern_kernel.rs"]
mod pattern_kernel;
#[path = "util.rs"]
mod util;

pub fn run() {
    util::cited(
        "McCool_SuperscalarSequence",
        "McCool, Robison, Reinders (2012), Superscalar Sequence",
    );
    let canonical: Vec<String> = vec!["i1".to_string(), "i2".to_string(), "i3".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_superscalar(&["i1", "i2", "i3"]);
    util::assert_canonical_eq("McCool_SuperscalarSequence", &canonical, &reproduction);
}
