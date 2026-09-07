//! trace-equivalence harness for VdA_CancellingPartialJoin.
//! Semantics source: Russell et al. (2016), WCP-32 Cancelling Partial Join
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
        "VdA_CancellingPartialJoin",
        "Russell et al. (2016), WCP-32 Cancelling Partial Join",
    );
    let canonical: Vec<String> = vec!["A1".to_string(), "A2".to_string(), "cancel".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_partial_join("A", 2, "cancel");
    util::assert_canonical_eq("VdA_CancellingPartialJoin", &canonical, &reproduction);
}
