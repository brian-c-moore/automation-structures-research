//! Five policy vocabularies used by the bounded workload study.
//!
//! The individual modules exercise selected local mechanisms. The
//! generic modality drivers interpret invocation ordering and otherwise
//! use fixed driver semantics; this crate does not establish that an
//! arbitrary five-axis cell produces a coherent execution.

pub mod dependencies;
pub mod entity_model;
pub mod invocation;
pub mod lifecycle;
pub mod topology;

pub use dependencies::DependencyPolicy;
pub use entity_model::EntityModel;
pub use invocation::InvocationPolicy;
pub use lifecycle::LifecyclePolicy;
pub use topology::TopologyPolicy;

/// A five-field local projection of a classification record. The
/// generic modality drivers interpret `invocation`; other fields are
/// available to workload predicates and policy-unit tests but are not
/// general runtime parameters.
#[derive(Debug, Clone)]
pub struct ConfigVector {
    pub invocation: InvocationPolicy,
    pub entity_model: EntityModel,
    pub topology: TopologyPolicy,
    pub dependencies: DependencyPolicy,
    pub lifecycle: LifecyclePolicy,
}

impl ConfigVector {
    /// Test helper: a neutral default cv suitable for tests that do
    /// not exercise specific policy values.
    pub fn default_for_test() -> Self {
        Self {
            invocation: InvocationPolicy::Fifo,
            entity_model: EntityModel::AnonymousOperator,
            topology: TopologyPolicy::DeclaredStatic,
            dependencies: DependencyPolicy::Fixed,
            lifecycle: LifecyclePolicy::Simple,
        }
    }
}

/// Non-cfg-gated constructor used by the integration tests. The
/// `default_for_test` constructor above is gated to `#[cfg(test)]`
/// inside the crate, so integration tests under `rust/tests/` can't
/// reach it. This is a public test helper for that use.
impl Default for ConfigVector {
    fn default() -> Self {
        Self {
            invocation: InvocationPolicy::Fifo,
            entity_model: EntityModel::AnonymousOperator,
            topology: TopologyPolicy::DeclaredStatic,
            dependencies: DependencyPolicy::Fixed,
            lifecycle: LifecyclePolicy::Simple,
        }
    }
}
