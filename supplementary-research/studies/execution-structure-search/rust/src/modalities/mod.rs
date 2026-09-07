//! Four modality drivers (docs/execution-modalities.md).
//!
//! Each driver configures the shared primitive set into a bounded
//! execution discipline. Output equivalence is asserted only by
//! workloads that explicitly place multiple compatible modalities in
//! one equivalence class.

pub mod fork_join;
pub mod sequential;
pub mod step_graph;
pub mod stream_graph;

pub use fork_join::run_fork_join;
pub use sequential::run_sequential;
pub use step_graph::run_step_graph;
pub use stream_graph::run_stream_graph;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Modality {
    Sequential,
    ForkJoin,
    StepGraph,
    StreamGraph,
}

impl Modality {
    pub fn parse(s: &str) -> Result<Self, String> {
        match s {
            "Sequential" => Ok(Modality::Sequential),
            "ForkJoin" => Ok(Modality::ForkJoin),
            // StepGraph_Cyclic was used by existing TOMLs as a marker
            // that the step-graph has cycles; the modality itself is
            // still StepGraph: the cycle is a workload-graph property,
            // not a different modality.
            "StepGraph" | "StepGraph_Cyclic" => Ok(Modality::StepGraph),
            "StreamGraph" => Ok(Modality::StreamGraph),
            other => Err(format!("unknown modality: {}", other)),
        }
    }
}
