//! The six load-bearing primitives for cryptography.
//!
//! **Vendored verbatim** from `supplementary-research/studies/domain-corpora/algorithms/rust/src/primitives/` and
//! `supplementary-research/studies/domain-corpora/algorithms/rust/src/candidates/`. Each primitive is in its own file
//! so the six-primitive build-requirements answer for cryptography is
//! visible in the module layout.
//!
//! Five of the six (`ResourceRegistry`, `TraversalEngine`,
//! `ActuationPass`, `Reduction`, `Bisection`) are shared with the
//! 87-algorithm classical corpus. `Sampler` is asymmetric — load-bearing
//! in cryptography (entropy reads, rejection sampling, witness
//! generation, RSA-PSS salts) and absent from the classical-corpus uses.
//! That asymmetry is the substantive cross-corpus result.
//!
//! The twelve other catalog primitives (governance: ConvergenceGovernor,
//! Budget, FederatedBudget, RateLimit, Signal, AuditSink,
//! QualityHierarchy, AllocationSnapshot; selection:
//! CompetitiveSelection in three modes; relational: PropagationPass,
//! RelationshipGraph, EquivalenceClass, BacktrackingTraversal) are
//! deliberately not vendored — the build doesn't need them. See the
//! TLA+ `unused/` specs for the structural demonstration.

pub mod actuation_pass;
pub mod bisection;
pub mod reduction;
pub mod resource_registry;
pub mod sampler;
pub mod traversal_engine;

// Flat re-exports so callers write `primitives::ResourceRegistry`.
pub use actuation_pass::ActuationPass;
pub use bisection::Bisection;
pub use reduction::Reduction;
pub use resource_registry::ResourceRegistry;
pub use sampler::Sampler;
pub use traversal_engine::TraversalEngine;
