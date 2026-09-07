//! trace-equivalence harness for Jantsch_Untimed.
//! Semantics source: Jantsch (2003) Modeling Embedded Systems, untimed MoC
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_untimed`,
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
        "Jantsch_Untimed",
        "Jantsch (2003) Modeling Embedded Systems, untimed MoC",
    );
    let canonical: Vec<String> = vec!["e1".to_string(), "e2".to_string(), "e3".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_untimed(&["e1", "e2", "e3"]);
    util::assert_canonical_eq("Jantsch_Untimed", &canonical, &reproduction);
}
