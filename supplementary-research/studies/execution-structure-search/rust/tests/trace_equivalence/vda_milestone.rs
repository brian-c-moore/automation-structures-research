//! trace-equivalence harness for VdA_Milestone.
//! Semantics source: Russell et al. (2016), WCP-18 Milestone
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_milestone`,
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
    util::cited("VdA_Milestone", "Russell et al. (2016), WCP-18 Milestone");
    let canonical: Vec<String> = vec!["A".to_string(), "milestone".to_string(), "B".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_milestone("A", "B");
    util::assert_canonical_eq("VdA_Milestone", &canonical, &reproduction);
}
