//! Readable structure implementations for the Formal Examples artifact.
//!
//! These implementations emit typed events and enforce runtime obligations. They are semantic
//! donors for the executable examples. They do not implement or refine the canonical TLA+ machines.

mod actuation;
mod budget;
mod error;
mod evidence;
mod fork_join;
mod memoization;
mod quality_hierarchy;
mod reduction;
mod relationship_graph;
mod resource_registry;
mod rooted_frontier;
mod select_then_actuate;
mod selection;
mod sequential;
mod snapshot;
mod step_graph;
mod trace;
mod traversal;

pub use actuation::ActuationPass;
pub use budget::{Budget, Bytes, Unit};
pub use error::StructureError;
pub use evidence::{
    evidence_content_identity, ArtifactFamily, AuthorityKind, CandidateControlBinding,
    CandidateShapeAssessment, ClaimBoundary, ConstructionAccount, ConstructionEdge,
    ConstructionNode, ConstructionOutcome, ConstructionStratum, ControlClass, ControlRecord,
    DacBaseRecord, EvidenceRegistry, EvidenceRole, InstanceDelta, MaterializedDacRecord,
    MemberEdgeControlBinding, NativeProblemRecord, OracleRecord, RecordDefinition,
    RelationAssuranceClass, RelationContract, RelyReplacement, SharedImplementationBinding,
    SourceAuthority, StrippedRole, TerritoryRecord,
};
pub use fork_join::ForkJoin;
pub use memoization::{
    memoization_subject, run_memoization, MemoNode, MemoizationControl, MemoizationProblem,
    MemoizationResult, MEMOIZATION_EDGES, MEMOIZATION_STRUCTURES,
};
pub use quality_hierarchy::{QualityHierarchy, QualityNode};
pub use reduction::{PathReduction, Reduction, Relaxation};
pub use relationship_graph::{Edge, RelationshipGraph};
pub use resource_registry::ResourceRegistry;
pub use rooted_frontier::{
    rooted_frontier_subject, run_bounded_frontier, run_minimum_frontier, BoundedFrontierControl,
    BoundedFrontierResult, FrontierCandidate, FrontierTarget, MinimumFrontierResult,
    RootedFrontierControl, BOUNDED_FRONTIER_EDGES, BOUNDED_FRONTIER_STRUCTURES,
    ROOTED_FRONTIER_EDGES, ROOTED_FRONTIER_STRUCTURES,
};
pub use select_then_actuate::{SelectThenActuate, SelectionActuationOutcome};
pub use selection::CompetitiveSelection;
pub use sequential::Sequential;
pub use snapshot::{AllocationRecord, AllocationSnapshot, SnapshotMode};
pub use step_graph::StepGraph;
pub use trace::{RecipeEdge, StructuralEvent, Structure, TraceLog};
pub use traversal::{FrontierItem, TraversalEngine};
