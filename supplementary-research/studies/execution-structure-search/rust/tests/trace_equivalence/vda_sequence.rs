//! trace-equivalence harness for VdA_Sequence.
//! Semantics source: Russell, van der Aalst, ter Hofstede (2016), WCP-1 Sequence
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_sequence`,
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
        "VdA_Sequence",
        "Russell, van der Aalst, ter Hofstede (2016), WCP-1 Sequence",
    );
    let canonical: Vec<String> = vec!["A".to_string(), "B".to_string(), "C".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_sequence(&["A", "B", "C"]);
    util::assert_canonical_eq("VdA_Sequence", &canonical, &reproduction);
}
