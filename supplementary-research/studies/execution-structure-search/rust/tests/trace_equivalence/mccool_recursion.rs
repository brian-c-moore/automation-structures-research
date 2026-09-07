//! trace-equivalence harness for McCool_Recursion.
//! Semantics source: McCool, Robison, Reinders (2012), Recursion
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_recursion`,
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
        "McCool_Recursion",
        "McCool, Robison, Reinders (2012), Recursion",
    );
    let canonical: Vec<String> = vec!["r1".to_string(), "r2".to_string(), "base".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_recursion(&["r1", "r2", "base"]);
    util::assert_canonical_eq("McCool_Recursion", &canonical, &reproduction);
}
