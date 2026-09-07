//! trace-equivalence harness for VdA_ArbitraryCycles.
//! Semantics source: Russell et al. (2016), WCP-10 Arbitrary Cycles
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_arbitrary_cycles`,
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
        "VdA_ArbitraryCycles",
        "Russell et al. (2016), WCP-10 Arbitrary Cycles",
    );
    let canonical: Vec<String> = vec![
        "A".to_string(),
        "B".to_string(),
        "A".to_string(),
        "B".to_string(),
    ];
    let reproduction: Vec<String> = pattern_kernel::run_arbitrary_cycles(&["A", "B"], 2);
    util::assert_canonical_eq("VdA_ArbitraryCycles", &canonical, &reproduction);
}
