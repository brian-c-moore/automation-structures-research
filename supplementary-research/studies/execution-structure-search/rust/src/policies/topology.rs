//! Topology policy (docs/execution-modalities.md).
//!
//! Specifies how the edge set of the work graph evolves over time.
//! Maps to TLA+ `TopologyPolicies.tla`.

use std::collections::{BTreeSet, HashMap};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TopologyPolicy {
    DeclaredStatic,
    DeclaredMutable,
    RuntimeAddressable,
    RuntimeAnonymous,
}

#[derive(Debug, Clone, Default)]
pub struct TopologyState {
    pub edges: BTreeSet<(String, String)>,
    pub refs: HashMap<String, BTreeSet<String>>,
    pub allowed: BTreeSet<(String, String)>,
}

impl TopologyState {
    pub fn new(allowed: BTreeSet<(String, String)>, policy: TopologyPolicy) -> Self {
        let edges = match policy {
            TopologyPolicy::DeclaredStatic | TopologyPolicy::DeclaredMutable => allowed.clone(),
            _ => BTreeSet::new(),
        };
        Self {
            edges,
            refs: HashMap::new(),
            allowed,
        }
    }

    pub fn try_swap(&mut self, edge: (String, String), policy: TopologyPolicy) -> bool {
        if policy != TopologyPolicy::DeclaredMutable {
            return false;
        }
        if !self.allowed.contains(&edge) {
            return false;
        }
        if self.edges.contains(&edge) {
            self.edges.remove(&edge);
        } else {
            self.edges.insert(edge);
        }
        true
    }

    pub fn try_learn_ref(&mut self, from: String, to: String, policy: TopologyPolicy) -> bool {
        if policy != TopologyPolicy::RuntimeAddressable {
            return false;
        }
        self.refs
            .entry(from.clone())
            .or_default()
            .insert(to.clone());
        self.edges.insert((from, to));
        true
    }

    pub fn try_add_anonymous(&mut self, edge: (String, String), policy: TopologyPolicy) -> bool {
        if policy != TopologyPolicy::RuntimeAnonymous {
            return false;
        }
        if !self.allowed.contains(&edge) {
            return false;
        }
        self.edges.insert(edge);
        true
    }

    /// Invariant: the edge set never escapes the allowed superset.
    pub fn check_bounded(&self) -> bool {
        self.edges.iter().all(|e| self.allowed.contains(e))
    }

    /// Invariant: in addressable mode, every edge is justified by a ref.
    pub fn check_addressable_consistency(&self, policy: TopologyPolicy) -> bool {
        if policy != TopologyPolicy::RuntimeAddressable {
            return true;
        }
        self.edges.iter().all(|(from, to)| {
            self.refs
                .get(from)
                .map(|peers| peers.contains(to))
                .unwrap_or(false)
        })
    }
}
