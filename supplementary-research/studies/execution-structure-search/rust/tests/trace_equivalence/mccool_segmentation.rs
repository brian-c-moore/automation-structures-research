//! trace-equivalence harness for McCool_Segmentation.
//! Semantics source: McCool, Robison, Reinders (2012), Segmentation
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_segmentation`,
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
        "McCool_Segmentation",
        "McCool, Robison, Reinders (2012), Segmentation",
    );
    let canonical: Vec<String> = vec!["seg0".to_string(), "seg1".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_segmentation(&["seg0", "seg1"]);
    util::assert_canonical_eq("McCool_Segmentation", &canonical, &reproduction);
}
