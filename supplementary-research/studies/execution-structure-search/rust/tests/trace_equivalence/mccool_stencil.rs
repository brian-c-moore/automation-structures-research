//! trace-equivalence harness for McCool_Stencil.
//! Semantics source: McCool, Robison, Reinders (2012), Stencil
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_stencil`,
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
        "McCool_Stencil",
        "McCool, Robison, Reinders (2012), Stencil",
    );
    let canonical: Vec<String> = vec!["s012".to_string(), "s123".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_stencil(&["s012", "s123"]);
    util::assert_canonical_eq("McCool_Stencil", &canonical, &reproduction);
}
