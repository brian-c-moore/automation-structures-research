//! trace-equivalence harness for McCool_Recurrence.
//! Semantics source: McCool, Robison, Reinders (2012), Recurrence
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_recurrence`,
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
        "McCool_Recurrence",
        "McCool, Robison, Reinders (2012), Recurrence",
    );
    let canonical: Vec<String> = vec!["f1".to_string(), "f2".to_string(), "f3".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_recurrence(&["f1", "f2", "f3"]);
    util::assert_canonical_eq("McCool_Recurrence", &canonical, &reproduction);
}
