//! Actor pattern encoding library (docs/execution-modalities.md).
//!
//! Actor patterns expressed as configurations of the streaming-graph
//! primitive set. The mapping (docs/execution-modalities.md):
//!
//! - mailbox        -> input queue
//! - send           -> emit-to-downstream
//! - stateful body  -> per-record processing function
//! - PIDs           -> runtime topology entries
//! - selective recv -> invocation pattern policy
//! - become         -> dependency hot-swap
//! - supervision    -> lifecycle policy
//!
//! This module provides:
//! - [`Actor`]            : a single actor (mailbox + behavior + PID)
//! - [`ActorSystem`]      : routes messages between actors
//! - [`SelectiveReceive`] : pattern-match invocation
//! - [`Become`]           : dependency hot-swap
//! - [`Supervisor`]       : restart on crash

pub mod become_;
pub mod mailbox;
pub mod selective_receive;
pub mod supervision;

pub use become_::{BecomeActor, BehaviorTag};
pub use mailbox::{Actor, ActorSystem, Pid};
pub use selective_receive::{MessagePattern, SelectiveReceiveActor};
pub use supervision::{RestartStrategy, Supervisor};
