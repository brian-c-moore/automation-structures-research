//! **EquivalenceClass**.
//!
//! **Motivation.** Partition a set into classes with fast "same class?"
//! and fast merge — Union-Find.
//!
//! **Definition.** Representative-set under `find` / `union`, with path
//! compression and union-by-rank.
//!
//! **Invariant.** The equivalence-relation laws (reflexive, symmetric,
//! transitive) plus rank monotonicity. The inverse-Ackermann amortised
//! bound is out of scope here and in the TLA+ track.
//!
//! **Recognition.** Kruskal's MST, connected components, Graph Valid
//! Tree, region merging, type unification.

pub struct EquivalenceClass {
    parent: Vec<usize>,
    rank: Vec<usize>,
    classes: usize,
}

impl EquivalenceClass {
    pub fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            rank: vec![0; n],
            classes: n,
        }
    }

    pub fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            let root = self.find(self.parent[x]);
            self.parent[x] = root; // path compression
        }
        self.parent[x]
    }

    /// Merge the classes of `a` and `b`. Returns `false` if they were
    /// already in the same class (the cycle-detection signal Kruskal /
    /// Graph-Valid-Tree rely on).
    pub fn union(&mut self, a: usize, b: usize) -> bool {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return false;
        }
        match self.rank[ra].cmp(&self.rank[rb]) {
            std::cmp::Ordering::Less => self.parent[ra] = rb,
            std::cmp::Ordering::Greater => self.parent[rb] = ra,
            std::cmp::Ordering::Equal => {
                self.parent[rb] = ra;
                self.rank[ra] += 1; // rank monotonicity
            }
        }
        self.classes -= 1;
        true
    }

    pub fn same(&mut self, a: usize, b: usize) -> bool {
        self.find(a) == self.find(b)
    }
    pub fn class_count(&self) -> usize {
        self.classes
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn transitivity_via_union() {
        let mut e = EquivalenceClass::new(4);
        assert!(e.union(0, 1));
        assert!(e.union(1, 2));
        assert!(e.same(0, 2)); // transitive
        assert!(!e.union(0, 2)); // already same -> cycle signal
        assert_eq!(e.class_count(), 2); // {0,1,2}, {3}
    }
}
