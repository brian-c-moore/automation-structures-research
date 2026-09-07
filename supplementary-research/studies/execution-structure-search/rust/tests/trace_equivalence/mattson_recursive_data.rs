//! trace-equivalence harness for Mattson_RecursiveData.
//! Semantics source: Mattson, Sanders, Massingill (2004), Recursive Data
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_sequence`,
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
        "Mattson_RecursiveData",
        "Mattson, Sanders, Massingill (2004), Recursive Data",
    );
    let canonical: Vec<String> = vec!["n1".to_string(), "n2".to_string(), "n3".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_sequence(&["n1", "n2", "n3"]);
    util::assert_canonical_eq("Mattson_RecursiveData", &canonical, &reproduction);
}
