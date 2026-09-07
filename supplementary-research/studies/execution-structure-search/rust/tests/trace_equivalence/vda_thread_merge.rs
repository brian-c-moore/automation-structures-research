//! trace-equivalence harness for VdA_ThreadMerge.
//! Semantics source: Russell et al. (2016), WCP-41 Thread Merge
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_thread_merge`,
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
        "VdA_ThreadMerge",
        "Russell et al. (2016), WCP-41 Thread Merge",
    );
    let canonical: Vec<String> = vec!["t1".to_string(), "t2".to_string(), "merge".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_thread_merge(&["t1", "t2"]);
    util::assert_canonical_eq("VdA_ThreadMerge", &canonical, &reproduction);
}
