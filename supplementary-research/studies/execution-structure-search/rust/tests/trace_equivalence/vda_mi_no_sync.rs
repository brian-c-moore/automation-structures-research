//! trace-equivalence harness for VdA_MI_NoSync.
//! Semantics source: Russell et al. (2016), WCP-12 Multiple Instances Without Synchronization
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_mi_no_sync`,
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
        "VdA_MI_NoSync",
        "Russell et al. (2016), WCP-12 Multiple Instances Without Synchronization",
    );
    let canonical: Vec<String> = vec!["A1".to_string(), "A2".to_string(), "A3".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_mi_no_sync("A", 3);
    util::assert_canonical_eq("VdA_MI_NoSync", &canonical, &reproduction);
}
