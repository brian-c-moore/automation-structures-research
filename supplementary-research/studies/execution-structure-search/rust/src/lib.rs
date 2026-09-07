//! Bounded execution-modality study implementation.
//!
//! This crate exercises four local workloads and selected mechanics.
//! It is not a framework reproduction suite and does not implement
//! every policy value recorded by the 134 classification TOMLs.
//!
//! Crate layout:
//!
//! - [`primitives`] — queues, operators, scheduler.
//! - [`policies`]   — five policy vocabularies and their local test
//!                    mechanisms:
//!                    invocation, entity_model, topology,
//!                    dependencies, lifecycle.
//! - [`modalities`] — four modality drivers (Sequential, ForkJoin,
//!                    StepGraph, StreamGraph) plus the Modality enum
//!                    with a `parse(&str)` constructor.
//! - [`workloads`]  — operator-graph workloads implementing the shared
//!                    `Workload` trait.
//! - [`actor`]      — actor entity-model implementations (docs/execution-modalities.md).
//! - [`config`]     — loader for the classification-record schema.
//! - [`harness`]    — bounded projection for four supported workload
//!                    names. Domain-specific policy strings may map
//!                    to a smaller local enum and receive no product
//!                    conformance or policy-fidelity credit.

pub mod actor;
pub mod config;
pub mod harness;
pub mod modalities;
pub mod policies;
pub mod primitives;
pub mod workloads;

pub use modalities::{run_fork_join, run_sequential, run_step_graph, run_stream_graph};
pub use workloads::data_pipeline::DataPipelineWorkload;
