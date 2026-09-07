//! trace-equivalence harness for McCool_Expand.
//! Semantics source: McCool, Robison, Reinders (2012), Expand
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_expand`,
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
    util::cited("McCool_Expand", "McCool, Robison, Reinders (2012), Expand");
    let canonical: Vec<String> = vec!["x1a".to_string(), "x1b".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_expand(&["x1a", "x1b"]);
    util::assert_canonical_eq("McCool_Expand", &canonical, &reproduction);
}
