//! The `AbstractionPrimitive` trait.
//!
//! This trait states the shared typed primitive signature:
//!
//! > a primitive takes a typed input, produces a typed output (or an
//! > invariant violation), and exposes its governance invariant.
//!
//! The shape is uniform across every primitive; only the domain-supplied
//! types and functions change. The invariant lives *inside* the
//! primitive — that is the governance boundary.

/// Returned when an operation would breach a primitive's governance
/// invariant. The primitive leaves its state unchanged (no partial
/// mutation). The irreducibility proofs establish that atomicity at the
/// primitive boundary is load-bearing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InvariantViolation(pub &'static str);

/// The uniform primitive signature.
pub trait AbstractionPrimitive {
    type Input;
    type Output;
    type Invariant;

    /// Apply the primitive. Either succeeds and updates state, or fails
    /// with an [`InvariantViolation`] and leaves state unchanged.
    fn apply(&mut self, input: Self::Input) -> Result<Self::Output, InvariantViolation>;

    /// Expose the governance invariant (numeric ceiling, state-machine
    /// property, hash-chain property, …) as data the caller can inspect.
    fn invariant(&self) -> Self::Invariant;
}
