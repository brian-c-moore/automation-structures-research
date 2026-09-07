//! trace-equivalence harness for VdA_ThreadSplit.
//! Semantics source: Russell et al. (2016), WCP-42 Thread Split
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_thread_split`,
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
        "VdA_ThreadSplit",
        "Russell et al. (2016), WCP-42 Thread Split",
    );
    let canonical: Vec<String> = vec!["A".to_string(), "t1".to_string(), "t2".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_thread_split("A", &["t1", "t2"]);
    util::assert_canonical_eq("VdA_ThreadSplit", &canonical, &reproduction);
}
