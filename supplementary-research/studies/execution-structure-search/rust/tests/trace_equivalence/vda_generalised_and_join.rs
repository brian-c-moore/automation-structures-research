//! trace-equivalence harness for VdA_GeneralisedAndJoin.
//! Semantics source: Russell et al. (2016), WCP-33 Generalised AND-Join
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_generalised_and_join`,
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
        "VdA_GeneralisedAndJoin",
        "Russell et al. (2016), WCP-33 Generalised AND-Join",
    );
    let canonical: Vec<String> = vec![
        "A".to_string(),
        "B".to_string(),
        "C".to_string(),
        "and".to_string(),
    ];
    let reproduction: Vec<String> = pattern_kernel::run_generalised_and_join(&["A", "B", "C"]);
    util::assert_canonical_eq("VdA_GeneralisedAndJoin", &canonical, &reproduction);
}
