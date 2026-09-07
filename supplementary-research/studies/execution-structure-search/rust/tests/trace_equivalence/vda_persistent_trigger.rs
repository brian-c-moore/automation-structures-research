//! trace-equivalence harness for VdA_PersistentTrigger.
//! Semantics source: Russell et al. (2016), WCP-24 Persistent Trigger
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_trigger`,
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
        "VdA_PersistentTrigger",
        "Russell et al. (2016), WCP-24 Persistent Trigger",
    );
    let canonical: Vec<String> = vec!["trigger".to_string(), "A".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_trigger("trigger", "A");
    util::assert_canonical_eq("VdA_PersistentTrigger", &canonical, &reproduction);
}
