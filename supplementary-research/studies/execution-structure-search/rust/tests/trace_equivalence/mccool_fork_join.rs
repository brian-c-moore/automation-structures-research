//! trace-equivalence harness for McCool_ForkJoin.
//! Semantics source: McCool, Robison, Reinders (2012), Fork-Join
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_fork_join_pattern`,
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
        "McCool_ForkJoin",
        "McCool, Robison, Reinders (2012), Fork-Join",
    );
    let canonical: Vec<String> = vec![
        "fork".to_string(),
        "w1".to_string(),
        "w2".to_string(),
        "join".to_string(),
    ];
    let reproduction: Vec<String> = pattern_kernel::run_fork_join_pattern(&["w1", "w2"]);
    util::assert_canonical_eq("McCool_ForkJoin", &canonical, &reproduction);
}
