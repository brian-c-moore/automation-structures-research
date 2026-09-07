//! trace-equivalence harness for Mattson_TaskParallelism.
//! Semantics source: Mattson, Sanders, Massingill (2004), Task Parallelism
//!
//! The canonical trace is derived from the cited semantics. The
//! reproduction trace is produced by `pattern_kernel::run_task_parallelism`,
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
        "Mattson_TaskParallelism",
        "Mattson, Sanders, Massingill (2004), Task Parallelism",
    );
    let canonical: Vec<String> = vec!["t1".to_string(), "t2".to_string(), "t3".to_string()];
    let reproduction: Vec<String> = pattern_kernel::run_task_parallelism(&["t1", "t2", "t3"]);
    util::assert_canonical_eq("Mattson_TaskParallelism", &canonical, &reproduction);
}
