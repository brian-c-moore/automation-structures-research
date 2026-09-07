//! trace-equivalence harness for VdA_MultiChoiceSyncMerge.
//! Semantics source: Russell et al. (2016), Multi-Choice + Synchronizing Merge
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_merge_variant`,
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
        "VdA_MultiChoiceSyncMerge",
        "Russell et al. (2016), Multi-Choice + Synchronizing Merge",
    );
    let canonical: Vec<String> = vec!["orB".to_string(), "orC".to_string(), "sync".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_merge_variant(&["orB", "orC"], "sync");
    util::assert_canonical_eq("VdA_MultiChoiceSyncMerge", &canonical, &reproduction);
}
