//! Data primitives: how data is structured and related.

use std::collections::HashMap;
use std::hash::Hash;

// ===================================================================
// ResourceRegistry<K, V>
// ===================================================================
/// **Motivation.** The most common operation in computation is "look up
/// a value by a key": hash maps, symbol tables, caches, memo tables,
/// visited sets, adjacency lists.
///
/// **Definition.** A typed key→value mapping with `insert`, `lookup`,
/// `delete`.
///
/// **Invariant.** Functional consistency: `lookup(k)` returns the most
/// recently inserted value for `k`, or `None` after delete / no insert.
///
/// **Recognition.** The workhorse of the corpus — as a presence set
/// (`V = ()`), a counter (`V = i64`), a memo (`V = result`), a graph
/// adjacency (`V = Vec<node>`).
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ResourceRegistry<K: Eq + Hash + Clone, V: Clone> {
    map: HashMap<K, V>,
}

impl<K: Eq + Hash + Clone, V: Clone> ResourceRegistry<K, V> {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }
    pub fn insert(&mut self, key: K, value: V) {
        self.map.insert(key, value);
    }
    pub fn lookup(&self, key: &K) -> Option<&V> {
        self.map.get(key)
    }
    pub fn contains(&self, key: &K) -> bool {
        self.map.contains_key(key)
    }
    pub fn delete(&mut self, key: &K) -> Option<V> {
        self.map.remove(key)
    }
    pub fn len(&self) -> usize {
        self.map.len()
    }
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
    pub fn entry_or(&mut self, key: K, default: V) -> &mut V {
        self.map.entry(key).or_insert(default)
    }
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.map.values()
    }
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.map.keys()
    }
    // Functional consistency is enforced by the HashMap representation:
    // there is exactly one current value per key. No runtime predicate is
    // exported for that representation guarantee.
}

// ===================================================================
// RelationshipGraph
// ===================================================================
/// **Motivation.** Many domains operate over typed graphs of entities.
///
/// **Definition.** A graph with typed nodes and (here, integer-labelled)
/// typed edges; node/edge insertion, neighbour queries.
///
/// **Invariant.** The adjacency view is consistent with the inserted
/// edge set (no dangling endpoint).
///
/// **Recognition.** Scene graphs, dependency graphs, computation graphs.
#[derive(Debug, Clone, Default)]
pub struct RelationshipGraph<N: Eq + Hash + Clone> {
    nodes: Vec<N>,
    adj: HashMap<N, Vec<N>>,
}

impl<N: Eq + Hash + Clone> RelationshipGraph<N> {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            adj: HashMap::new(),
        }
    }
    pub fn add_node(&mut self, n: N) {
        if !self.adj.contains_key(&n) {
            self.nodes.push(n.clone());
            self.adj.insert(n, Vec::new());
        }
    }
    pub fn add_edge(&mut self, a: N, b: N) {
        self.add_node(a.clone());
        self.add_node(b.clone());
        self.adj.get_mut(&a).unwrap().push(b);
    }
    pub fn neighbours(&self, n: &N) -> &[N] {
        self.adj.get(n).map(|v| v.as_slice()).unwrap_or(&[])
    }
    pub fn nodes(&self) -> &[N] {
        &self.nodes
    }
    /// Invariant: every adjacency endpoint is a registered node.
    pub fn invariant(&self) -> bool {
        self.adj
            .values()
            .flatten()
            .all(|b| self.adj.contains_key(b))
    }
}

// ===================================================================
// QualityHierarchy
// ===================================================================
/// **Motivation.** Same conceptual data at multiple fidelity levels.
///
/// **Definition.** A rooted chain of refinements (level 0 coarsest);
/// `promote` toward detail, `demote` back.
///
/// **Invariant.** The current level is within `[0, depth)`; each level
/// refines its parent (modelled here as monotone level index).
///
/// **Recognition.** LOD systems, OSPF areas, ML parameter groups. Not
/// exercised by the classical corpus.
#[derive(Debug, Clone)]
pub struct QualityHierarchy {
    depth: usize,
    level: usize,
}
impl QualityHierarchy {
    pub fn new(depth: usize) -> Self {
        Self { depth, level: 0 }
    }
    pub fn promote(&mut self) -> bool {
        if self.level + 1 < self.depth {
            self.level += 1;
            true
        } else {
            false
        }
    }
    pub fn demote(&mut self) -> bool {
        if self.level > 0 {
            self.level -= 1;
            true
        } else {
            false
        }
    }
    pub fn level(&self) -> usize {
        self.level
    }
    pub fn invariant(&self) -> bool {
        self.level < self.depth
    }
}

// ===================================================================
// AllocationSnapshot
// ===================================================================
/// **Motivation.** An allocation decision recorded immutably so
/// downstream consumers can rely on it.
///
/// **Definition.** An immutable record of an assignment.
///
/// **Invariant.** Once produced, never changes (enforced: no mutators).
#[derive(Debug, Clone)]
pub struct AllocationSnapshot<T: Clone> {
    record: T,
}
impl<T: Clone> AllocationSnapshot<T> {
    pub fn capture(record: T) -> Self {
        Self { record }
    }
    pub fn read(&self) -> &T {
        &self.record
    }
    // Immutability is enforced by the API: the captured record is private and
    // this type exports no mutator. No runtime predicate is needed.
}

// ===================================================================
// Budget<U>: hard-capacity accounting primitive.
// ===================================================================
/// **Motivation.** Bound a consumed resource by a structural ceiling.
///
/// **Definition / Invariant.** `consumed <= capacity` at every
/// observable state; `try_allocate` is all-or-nothing. There is no
/// `force_allocate`.
///
/// **Recognition.** GPU/VRAM ceilings, container limits, LoRA parameter
/// caps. Not exercised by the classical corpus.
#[derive(Debug, Clone)]
pub struct Budget {
    capacity: u64,
    allocated: u64,
}
impl Budget {
    pub fn new(capacity: u64) -> Self {
        Self {
            capacity,
            allocated: 0,
        }
    }
    pub fn try_allocate(&mut self, amount: u64) -> bool {
        if self.allocated + amount > self.capacity {
            return false;
        }
        self.allocated += amount;
        true
    }
    pub fn release(&mut self, amount: u64) {
        self.allocated = self.allocated.saturating_sub(amount);
    }
    pub fn available(&self) -> u64 {
        self.capacity - self.allocated
    }
    /// The governance invariant, as inspectable data.
    pub fn invariant(&self) -> bool {
        self.allocated <= self.capacity
    }
}

// ===================================================================
// FederatedBudget<U>
// ===================================================================
/// **Motivation.** Sub-pools sharing a master pool.
///
/// **Definition.** A master capacity subdivided per child.
///
/// **Invariant.** `sum(child.consumed) <= master.capacity`.
///
/// **Recognition.** k8s namespace quotas, cgroup hierarchies.
#[derive(Debug, Clone)]
pub struct FederatedBudget {
    master: u64,
    children: HashMap<String, u64>,
}
impl FederatedBudget {
    pub fn new(master: u64) -> Self {
        Self {
            master,
            children: HashMap::new(),
        }
    }
    pub fn allocate_to_child(&mut self, child: &str, amount: u64) -> bool {
        let total: u64 = self.children.values().sum();
        if total + amount > self.master {
            return false;
        }
        *self.children.entry(child.to_string()).or_insert(0) += amount;
        true
    }
    pub fn invariant(&self) -> bool {
        self.children.values().sum::<u64>() <= self.master
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn budget_ceiling_holds() {
        let mut b = Budget::new(4);
        assert!(b.try_allocate(3));
        assert!(!b.try_allocate(2)); // would exceed
        assert!(b.invariant());
    }
    #[test]
    fn federated_sum_invariant_holds() {
        let mut fb = FederatedBudget::new(10);
        assert!(fb.allocate_to_child("a", 6));
        assert!(!fb.allocate_to_child("b", 5));
        assert!(fb.invariant());
    }
    #[test]
    fn registry_functional_consistency() {
        let mut r: ResourceRegistry<i32, i32> = ResourceRegistry::new();
        r.insert(1, 10);
        r.insert(1, 20);
        assert_eq!(r.lookup(&1), Some(&20));
    }
}
