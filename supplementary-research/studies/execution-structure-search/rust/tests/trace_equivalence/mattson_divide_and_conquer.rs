//! trace-equivalence harness for Mattson_DivideAndConquer.
//! Semantics source: Mattson, Sanders, Massingill (2004), Divide-and-Conquer
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_divide_and_conquer`,
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
        "Mattson_DivideAndConquer",
        "Mattson, Sanders, Massingill (2004), Divide-and-Conquer",
    );
    let canonical: Vec<String> = vec![
        "split".to_string(),
        "l".to_string(),
        "r".to_string(),
        "merge".to_string(),
    ];
    let reproduction: Vec<String> = pattern_kernel::run_divide_and_conquer("l", "r");
    util::assert_canonical_eq("Mattson_DivideAndConquer", &canonical, &reproduction);
}
