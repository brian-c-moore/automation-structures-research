//! trace-equivalence harness for VdA_MultiChoice.
//! Semantics source: Russell et al. (2016), WCP-6 Multi-Choice
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_multi_choice`,
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
        "VdA_MultiChoice",
        "Russell et al. (2016), WCP-6 Multi-Choice",
    );
    let canonical: Vec<String> = vec!["A".to_string(), "orB".to_string(), "orC".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_multi_choice("A", &["B", "C"]);
    util::assert_canonical_eq("VdA_MultiChoice", &canonical, &reproduction);
}
