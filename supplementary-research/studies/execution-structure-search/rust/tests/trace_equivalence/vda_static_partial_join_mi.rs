//! trace-equivalence harness for VdA_StaticPartialJoinMI.
//! Semantics source: Russell et al. (2016), WCP-34 Static Partial Join for MI
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_partial_join`,
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
        "VdA_StaticPartialJoinMI",
        "Russell et al. (2016), WCP-34 Static Partial Join for MI",
    );
    let canonical: Vec<String> = vec!["A1".to_string(), "A2".to_string(), "static".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_partial_join("A", 2, "static");
    util::assert_canonical_eq("VdA_StaticPartialJoinMI", &canonical, &reproduction);
}
