//! The canonical primitive set, grouped as data, control, and
//! coordination.
//!
//! Each primitive is documented in the *motivation, definition, invariant,
//! recognition* idiom. `Budget` and `ConvergenceGovernor` reuse the catalog
//! definitions; the remaining modules state their definitions and
//! invariants locally.
//!
//! The classical algorithm corpus exercises the
//! **data and control** primitives heavily and, by construction, does
//! not use the **coordination/governance** primitives — algorithms in
//! isolation have no resource bounds, audit, or cross-component
//! coordination. The governance primitives are included here, faithful
//! to spec, as part of the canonical teaching set and for completeness.

pub mod control;
pub mod coordination;
pub mod data;

// Flat re-exports so callers write `primitives::ResourceRegistry`.
pub use control::{
    ActuationPass, CompetitiveSelection, PriorityQueue, PropagationPass, Reduction, Sampler,
    SelectionMode, TraversalEngine,
};
pub use coordination::{AuditSink, ConvergenceGovernor, ConvergenceState, RateLimit, Signal};
pub use data::{
    AllocationSnapshot, Budget, FederatedBudget, QualityHierarchy, RelationshipGraph,
    ResourceRegistry,
};
