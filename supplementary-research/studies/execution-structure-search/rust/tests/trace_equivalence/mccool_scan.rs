//! trace-equivalence harness for McCool_Scan.
//! Semantics source: McCool, Robison, Reinders (2012), Scan
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_scan`,
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
    util::cited("McCool_Scan", "McCool, Robison, Reinders (2012), Scan");
    let canonical: Vec<String> = vec![
        "p1".to_string(),
        "p1+p2".to_string(),
        "p1+p2+p3".to_string(),
    ];
    let reproduction: Vec<String> = pattern_kernel::run_scan(&["p1", "p1+p2", "p1+p2+p3"]);
    util::assert_canonical_eq("McCool_Scan", &canonical, &reproduction);
}
