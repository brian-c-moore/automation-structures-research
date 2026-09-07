//! Dependency policy (docs/execution-modalities.md).
//!
//! Whether and how the per-operator function may change over time.
//! Maps to TLA+ `DependencyPolicies.tla`.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DependencyPolicy {
    Fixed,
    HotSwappable,
    Conditional,
}

pub struct BehaviorSlot<I, O> {
    pub current: Box<dyn Fn(I) -> O + Send + Sync>,
    pub policy: DependencyPolicy,
    pub swap_count: usize,
}

impl<I, O> BehaviorSlot<I, O> {
    pub fn new(initial: Box<dyn Fn(I) -> O + Send + Sync>, policy: DependencyPolicy) -> Self {
        Self {
            current: initial,
            policy,
            swap_count: 0,
        }
    }

    /// Erlang-style `become`: swap the operator function. Only valid
    /// under HotSwappable or Conditional. Returns whether the swap
    /// happened.
    pub fn try_become(&mut self, new_fn: Box<dyn Fn(I) -> O + Send + Sync>) -> bool {
        match self.policy {
            DependencyPolicy::Fixed => false,
            DependencyPolicy::HotSwappable | DependencyPolicy::Conditional => {
                self.current = new_fn;
                self.swap_count += 1;
                true
            }
        }
    }

    pub fn invoke(&self, input: I) -> O {
        (self.current)(input)
    }

    /// Invariant: under Fixed, swap_count stays at 0.
    pub fn check_fixed_no_change(&self) -> bool {
        match self.policy {
            DependencyPolicy::Fixed => self.swap_count == 0,
            _ => true,
        }
    }
}
