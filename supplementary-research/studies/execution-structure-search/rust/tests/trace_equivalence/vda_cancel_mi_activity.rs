//! trace-equivalence harness for VdA_CancelMIActivity.
//! Semantics source: Russell et al. (2016), WCP-26 Cancel Multiple Instance Activity
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_cancel_mi_activity`,
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
        "VdA_CancelMIActivity",
        "Russell et al. (2016), WCP-26 Cancel Multiple Instance Activity",
    );
    let canonical: Vec<String> = vec!["A1".to_string(), "cancel".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_cancel_mi_activity("A", 1);
    util::assert_canonical_eq("VdA_CancelMIActivity", &canonical, &reproduction);
}
