//! Scheduling primitive.
//!
//! Maps to the implicit "step relation" of each modality TLA+ spec.
//! The scheduler determines, given a set of nodes/operators and their
//! current state, which one is eligible to advance next. Different
//! modalities install different eligibility predicates.
//!
//! The scheduler is intentionally policy-free at this layer; the
//! invocation-policy axis composes on top.

use crate::primitives::operator::OperatorState;

pub struct Scheduler;

impl Scheduler {
    /// Step-graph eligibility: a node becomes Ready when all its
    /// predecessors are Completed.
    pub fn step_graph_eligible(
        node_state: &OperatorState,
        predecessor_states: &[OperatorState],
    ) -> bool {
        matches!(node_state, OperatorState::NotReady)
            && predecessor_states
                .iter()
                .all(|s| matches!(s, OperatorState::Completed))
    }

    /// Stream-graph eligibility: an operator can fire when it has
    /// input AND all output queues have room (no backpressure).
    pub fn stream_graph_eligible(input_available: bool, output_has_room: bool) -> bool {
        input_available && output_has_room
    }

    /// Fork-join eligibility: in the parallel phase, every worker is
    /// independently eligible. After the barrier, only the join step.
    pub fn fork_join_worker_eligible(state: &OperatorState) -> bool {
        matches!(state, OperatorState::Ready | OperatorState::Running)
    }

    /// Sequential eligibility: the next step is the one whose pc =
    /// the current pc + 1, and only if no step is currently active.
    pub fn sequential_eligible(active: bool, pc: usize, next_pc: usize) -> bool {
        !active && next_pc == pc + 1
    }
}
