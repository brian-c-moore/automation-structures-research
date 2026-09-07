//! trace-equivalence harness for McCool_Partition.
//! Semantics source: McCool, Robison, Reinders (2012), Partition
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_partition`,
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
        "McCool_Partition",
        "McCool, Robison, Reinders (2012), Partition",
    );
    let canonical: Vec<String> = vec!["p0".to_string(), "p1".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_partition(&["p0", "p1"]);
    util::assert_canonical_eq("McCool_Partition", &canonical, &reproduction);
}
