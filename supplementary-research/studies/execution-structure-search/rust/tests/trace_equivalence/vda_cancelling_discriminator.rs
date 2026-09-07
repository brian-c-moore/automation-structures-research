//! trace-equivalence harness for VdA_CancellingDiscriminator.
//! Semantics source: Russell et al. (2016), WCP-29 Cancelling Discriminator
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_cancelling_discriminator`,
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
        "VdA_CancellingDiscriminator",
        "Russell et al. (2016), WCP-29 Cancelling Discriminator",
    );
    let canonical: Vec<String> = vec!["firstB".to_string(), "cancelOthers".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_cancelling_discriminator(&["B"]);
    util::assert_canonical_eq("VdA_CancellingDiscriminator", &canonical, &reproduction);
}
