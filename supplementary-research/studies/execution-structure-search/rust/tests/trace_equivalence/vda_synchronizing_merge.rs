//! trace-equivalence harness for VdA_SynchronizingMerge.
//! Semantics source: Russell et al. (2016), WCP-7 Structured Synchronizing Merge
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_synchronizing_merge`,
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
        "VdA_SynchronizingMerge",
        "Russell et al. (2016), WCP-7 Structured Synchronizing Merge",
    );
    let canonical: Vec<String> = vec!["B".to_string(), "C".to_string(), "sm".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_synchronizing_merge(&["B", "C"]);
    util::assert_canonical_eq("VdA_SynchronizingMerge", &canonical, &reproduction);
}
