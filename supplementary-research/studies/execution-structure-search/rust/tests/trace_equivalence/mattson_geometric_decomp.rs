//! trace-equivalence harness for Mattson_GeometricDecomp.
//! Semantics source: Mattson, Sanders, Massingill (2004), Geometric Decomposition
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_geometric_decomp`,
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
        "Mattson_GeometricDecomp",
        "Mattson, Sanders, Massingill (2004), Geometric Decomposition",
    );
    let canonical: Vec<String> = vec![
        "chunk0".to_string(),
        "chunk1".to_string(),
        "exchange".to_string(),
    ];
    let reproduction: Vec<String> =
        pattern_kernel::run_geometric_decomp(&["chunk0", "chunk1"], "exchange");
    util::assert_canonical_eq("Mattson_GeometricDecomp", &canonical, &reproduction);
}
