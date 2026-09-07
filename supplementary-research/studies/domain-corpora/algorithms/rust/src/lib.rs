//! # Algorithms corpus — a primitive set and its instantiations
//!
//! Executable algorithm-reconstruction corpus over shared primitive modules
//! with independent Python oracle comparisons.
//!
//! ## The three axes, made concrete in code
//!
//! The corpus taxonomy classifies any algorithm on three independent axes. This
//! crate makes each one inspectable:
//!
//! - **Components** — [`primitives`] and [`candidates`]. One module per
//!   catalog primitive, each documented in the
//!   *motivation / definition / invariant / recognition* idiom. The
//!   invariant is enforced in the type, not in caller code: that is what
//!   makes it a primitive rather than a convention.
//! - **Structural ordering** — every algorithm in [`compositions`] names
//!   its ordering (Linear / Tree / DAG / Graph-with-cycles) in its doc
//!   comment. The ordering is a property of how the operations depend on
//!   each other, not of how they were coded.
//! - **Execution modality** — the corpus is executed Sequentially here;
//!   each composition records which higher modalities its ordering
//!   *admits* (the admission table, formally verified in
//!   `supplementary-research/studies/domain-corpora/algorithms/tla/admission/`).
//!
//! ## Reuse, not regeneration
//!
//! [`primitives::budget`] and [`primitives::convergence_governor`] reuse the
//! catalog definitions. [`AbstractionPrimitive`] provides the shared
//! typed signature. Every other primitive states its governing invariant
//! in its own module.
//!
//! ## Shared definitions
//!
//! Every corpus algorithm in [`compositions`] is built *only* from
//! [`primitives`] / [`candidates`] — no algorithm re-implements primitive
//! logic. The harness, the equivalence relations, the Python-oracle
//! bridge, and the manifest loader each exist exactly once
//! ([`harness`], [`equivalence`], [`oracle`], [`config`]).
//!
//! ## Layout (mirrors `supplementary-research/studies/execution-structure-search/rust/`)
//!
//! - [`primitive`]   — the `AbstractionPrimitive` trait.
//! - [`primitives`]  — the canonical sixteen-primitive set.
//! - [`candidates`]  — Bisection, EquivalenceClass.
//! - [`compositions`]— the algorithm corpus, one fn per algorithm.
//! - [`equivalence`] — exact / set / multiset / validity / float / structural.
//! - [`oracle`]      — bridge to the idiomatic Python references.
//! - [`config`]      — `tests.toml` manifest loader.
//! - [`harness`]     — input generation, dual run, comparison, recording.

pub mod candidates;
pub mod compositions;
pub mod config;
pub mod equivalence;
pub mod harness;
pub mod oracle;
pub mod primitive;
pub mod primitives;
pub mod value;

pub use primitive::AbstractionPrimitive;
pub use value::Value;
