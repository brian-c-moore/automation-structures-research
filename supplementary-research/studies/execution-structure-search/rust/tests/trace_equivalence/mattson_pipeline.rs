//! trace-equivalence harness for Mattson_Pipeline.
//! Semantics source: Mattson, Sanders, Massingill (2004), Pipeline
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
        "Mattson_Pipeline",
        "Mattson, Sanders, Massingill (2004), Pipeline",
    );
    let canonical: Vec<String> = vec!["s1".to_string(), "s2".to_string(), "s3".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_pipeline(&["s1", "s2", "s3"]);
    util::assert_canonical_eq("Mattson_Pipeline", &canonical, &reproduction);
}
