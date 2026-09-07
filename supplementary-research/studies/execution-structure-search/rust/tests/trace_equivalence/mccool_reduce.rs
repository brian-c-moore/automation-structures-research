//! trace-equivalence harness for McCool_Reduce.
//! Semantics source: McCool, Robison, Reinders (2012), Reduce
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_reduce`,
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
    util::cited("McCool_Reduce", "McCool, Robison, Reinders (2012), Reduce");
    let canonical: Vec<String> = vec!["partial1".to_string(), "total".to_string()];
    let reproduction: Vec<String> =
        pattern_kernel::run_reduce(&["x1", "x2", "x3"], &["partial1", "total"]);
    util::assert_canonical_eq("McCool_Reduce", &canonical, &reproduction);
}
