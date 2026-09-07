//! Coordination primitives: how the system observes and governs itself.
//! These do not appear in classical algorithms in isolation; they are part
//! of the canonical teaching set and faithful to spec, but the corpus does
//! not exercise them.

use std::collections::VecDeque;

// ===================================================================
// Signal<T>
// ===================================================================
/// **Motivation.** Decoupled producer→consumer events without polling.
///
/// **Definition.** Typed fan-out channel: `emit` reaches every active
/// subscriber.
///
/// **Invariant.** Delivery: every emitted event reaches every subscriber.
pub struct Signal<T> {
    subscribers: Vec<Box<dyn FnMut(&T)>>,
}
impl<T> Signal<T> {
    pub fn new() -> Self {
        Self {
            subscribers: Vec::new(),
        }
    }
    pub fn subscribe<F: FnMut(&T) + 'static>(&mut self, f: F) {
        self.subscribers.push(Box::new(f));
    }
    pub fn emit(&mut self, event: T) {
        for s in self.subscribers.iter_mut() {
            s(&event);
        }
    }
}
impl<T> Default for Signal<T> {
    fn default() -> Self {
        Self::new()
    }
}

// ===================================================================
// RateLimit
// ===================================================================
/// **Motivation.** Cap a *rate* (per window), distinct from a total cap.
///
/// **Definition.** Token bucket: capacity `cap`, refilled by `refill`
/// each `tick`.
///
/// **Invariant.** Throughput within a window never exceeds `cap`.
#[derive(Debug, Clone)]
pub struct RateLimit {
    cap: u64,
    tokens: u64,
    refill: u64,
}
impl RateLimit {
    pub fn new(cap: u64, refill: u64) -> Self {
        Self {
            cap,
            tokens: cap,
            refill,
        }
    }
    pub fn try_consume(&mut self, amount: u64) -> bool {
        if amount <= self.tokens {
            self.tokens -= amount;
            true
        } else {
            false
        }
    }
    pub fn tick(&mut self) {
        self.tokens = (self.tokens + self.refill).min(self.cap);
    }
    pub fn invariant(&self) -> bool {
        self.tokens <= self.cap
    }
}

// ===================================================================
// ConvergenceGovernor: convergence-state coordination primitive.
// ===================================================================
/// **Motivation.** Robust fixed-point detection from observed deltas
/// (false positives and false negatives both have consequences).
///
/// **Definition / Invariant.** The four-state machine ACTIVE → COOLING
/// → CONVERGED, with AWAKENED on perturbation; it never skips a state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConvergenceState {
    Active,
    Cooling,
    Converged,
    Awakened,
}
#[derive(Debug, Clone)]
pub struct ConvergenceGovernor {
    state: ConvergenceState,
    delta_history: VecDeque<f64>,
    threshold: f64,
    window: usize,
}
impl ConvergenceGovernor {
    pub fn new(threshold: f64, window: usize) -> Self {
        Self {
            state: ConvergenceState::Active,
            delta_history: VecDeque::new(),
            threshold,
            window,
        }
    }
    pub fn update(&mut self, delta: f64) -> ConvergenceState {
        self.delta_history.push_back(delta);
        if self.delta_history.len() > self.window {
            self.delta_history.pop_front();
        }
        let avg: f64 = self.delta_history.iter().sum::<f64>() / self.delta_history.len() as f64;
        self.state = match self.state {
            ConvergenceState::Active if avg < self.threshold * 2.0 => ConvergenceState::Cooling,
            ConvergenceState::Cooling if avg < self.threshold => ConvergenceState::Converged,
            ConvergenceState::Converged if avg > self.threshold * 3.0 => ConvergenceState::Awakened,
            ConvergenceState::Awakened if avg < self.threshold => ConvergenceState::Converged,
            other => other,
        };
        self.state
    }
    pub fn state(&self) -> ConvergenceState {
        self.state
    }
}

// ===================================================================
// AuditSink
// ===================================================================
/// **Motivation.** Tamper-evident, ordered record of every mutation.
///
/// **Definition.** Append-only log where each record carries a hash of
/// the previous record.
///
/// **Invariant.** Chain integrity: unbroken from genesis to head.
#[derive(Debug, Clone)]
pub struct AuditSink {
    chain: Vec<(u64, String)>, // (prev_hash, record)
}
impl AuditSink {
    pub fn new() -> Self {
        Self { chain: Vec::new() }
    }
    fn fnv1a(seed: u64, s: &str) -> u64 {
        let mut h = seed ^ 0xcbf29ce484222325;
        for b in s.bytes() {
            h ^= b as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
        h
    }
    pub fn append(&mut self, record: &str) {
        let prev = self.chain.last().map(|(h, _)| *h).unwrap_or(0);
        let h = Self::fnv1a(prev, record);
        self.chain.push((h, record.to_string()));
    }
    /// Recompute the chain and confirm it is unbroken.
    pub fn invariant(&self) -> bool {
        let mut prev = 0u64;
        for (h, r) in &self.chain {
            if *h != Self::fnv1a(prev, r) {
                return false;
            }
            prev = *h;
        }
        true
    }
    pub fn len(&self) -> usize {
        self.chain.len()
    }
}
impl Default for AuditSink {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn governor_never_skips_a_state() {
        let mut g = ConvergenceGovernor::new(0.1, 5);
        // Active -> Cooling -> Converged, in order, never skipping.
        // avg(0.15)=0.15 < 2*thr=0.2  => Cooling
        // avg(0.15,0.02)=0.085 < thr=0.1 => Converged (no state skipped)
        assert_eq!(g.update(0.15), ConvergenceState::Cooling);
        assert_eq!(g.update(0.02), ConvergenceState::Converged);
    }
    #[test]
    fn audit_chain_integrity_holds() {
        let mut a = AuditSink::new();
        a.append("alloc 3");
        a.append("release 1");
        assert!(a.invariant());
        assert_eq!(a.len(), 2);
    }
    #[test]
    fn ratelimit_window_cap() {
        let mut r = RateLimit::new(2, 1);
        assert!(r.try_consume(2));
        assert!(!r.try_consume(1));
        r.tick();
        assert!(r.try_consume(1));
        assert!(r.invariant());
    }
}
