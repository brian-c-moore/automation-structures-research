//! trace-equivalence harness for Jantsch_TightlyCoupled.
//! Semantics source: Jantsch (2003) Modeling Embedded Systems, tightly-coupled PN
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_tightly_coupled`,
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
        "Jantsch_TightlyCoupled",
        "Jantsch (2003) Modeling Embedded Systems, tightly-coupled PN",
    );
    let canonical: Vec<String> = vec!["p1>p2:e1".to_string(), "p2>p1:ack1".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_tightly_coupled();
    util::assert_canonical_eq("Jantsch_TightlyCoupled", &canonical, &reproduction);
}
