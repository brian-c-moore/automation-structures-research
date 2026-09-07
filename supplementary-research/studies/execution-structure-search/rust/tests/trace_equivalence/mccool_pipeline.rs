//! trace-equivalence harness for McCool_Pipeline.
//! Semantics source: McCool, Robison, Reinders (2012), Pipeline
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_pipeline`,
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
        "McCool_Pipeline",
        "McCool, Robison, Reinders (2012), Pipeline",
    );
    let canonical: Vec<String> = vec!["s1".to_string(), "s2".to_string(), "s3".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_pipeline(&["s1", "s2", "s3"]);
    util::assert_canonical_eq("McCool_Pipeline", &canonical, &reproduction);
}
