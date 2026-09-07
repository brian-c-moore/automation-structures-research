//! Shared primitive set used by all four modalities (docs/execution-modalities.md).
//!
//! Stream-graph propagation is implemented per record in the modality
//! driver. No separate propagation primitive participates in execution.

pub mod operator;
pub mod queue;
pub mod scheduler;

pub use operator::{Operator, OperatorFn, OperatorState};
pub use queue::{BoundedQueue, QueueError};
pub use scheduler::Scheduler;
