//! trace-equivalence harness for VdA_CriticalSection.
//! Semantics source: Russell et al. (2016), WCP-37 Critical Section
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_critical_section`,
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
        "VdA_CriticalSection",
        "Russell et al. (2016), WCP-37 Critical Section",
    );
    let canonical: Vec<String> = vec!["enter".to_string(), "A".to_string(), "exit".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_critical_section("A");
    util::assert_canonical_eq("VdA_CriticalSection", &canonical, &reproduction);
}
