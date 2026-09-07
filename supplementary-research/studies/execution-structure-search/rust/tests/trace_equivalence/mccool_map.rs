//! trace-equivalence harness for McCool_Map.
//! Semantics source: McCool, Robison, Reinders (2012), Map
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_map`,
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
    util::cited("McCool_Map", "McCool, Robison, Reinders (2012), Map");
    let canonical: Vec<String> = vec![
        "m(x1)".to_string(),
        "m(x2)".to_string(),
        "m(x3)".to_string(),
    ];
    let reproduction: Vec<String> = pattern_kernel::run_map(&["x1", "x2", "x3"]);
    util::assert_canonical_eq("McCool_Map", &canonical, &reproduction);
}
