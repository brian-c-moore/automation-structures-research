//! trace-equivalence harness for Jantsch_Synchronous.
//! Semantics source: Jantsch (2003) Modeling Embedded Systems, synchronous MoC
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_synchronous`,
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
        "Jantsch_Synchronous",
        "Jantsch (2003) Modeling Embedded Systems, synchronous MoC",
    );
    let canonical: Vec<String> = vec![
        "tick:e1".to_string(),
        "tick:e2".to_string(),
        "tick:e3".to_string(),
    ];
    let reproduction: Vec<String> = pattern_kernel::run_synchronous(&["e1", "e2", "e3"]);
    util::assert_canonical_eq("Jantsch_Synchronous", &canonical, &reproduction);
}
