use crate::{
    RecipeEdge, Reduction, ResourceRegistry, Structure, StructureError, TraceLog, TraversalEngine,
};
use serde::Serialize;
use std::collections::BTreeSet;

pub const MEMOIZATION_STRUCTURES: [Structure; 3] = [
    Structure::ResourceRegistry,
    Structure::TraversalEngine,
    Structure::Reduction,
];

pub const MEMOIZATION_EDGES: [RecipeEdge; 4] = [
    RecipeEdge {
        before: Structure::ResourceRegistry,
        before_action: "Commit",
        after: Structure::TraversalEngine,
        after_action: "Initialize",
    },
    RecipeEdge {
        before: Structure::TraversalEngine,
        before_action: "Visit",
        after: Structure::Reduction,
        after_action: "Commit",
    },
    RecipeEdge {
        before: Structure::Reduction,
        before_action: "Commit",
        after: Structure::ResourceRegistry,
        after_action: "Store",
    },
    RecipeEdge {
        before: Structure::ResourceRegistry,
        before_action: "Store",
        after: Structure::TraversalEngine,
        after_action: "Complete",
    },
];

pub fn memoization_subject(scope: &str) -> String {
    format!("{scope}::memoization")
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct MemoNode<S> {
    id: String,
    dependencies: Vec<String>,
    state: S,
}

impl<S> MemoNode<S> {
    pub fn new(
        id: impl Into<String>,
        dependencies: Vec<String>,
        state: S,
    ) -> Result<Self, StructureError> {
        let id = id.into();
        if id.is_empty() {
            return Err(StructureError::new("memoization node has an empty ID"));
        }
        let mut observed = BTreeSet::new();
        if dependencies
            .iter()
            .any(|dependency| dependency.is_empty() || !observed.insert(dependency))
        {
            return Err(StructureError::new(
                "memoization dependencies must be nonempty and unique",
            ));
        }
        if observed.contains(&id) {
            return Err(StructureError::new(
                "memoization node cannot depend on itself",
            ));
        }
        Ok(Self {
            id,
            dependencies,
            state,
        })
    }

    pub fn id(&self) -> &str {
        &self.id
    }

    pub fn dependencies(&self) -> &[String] {
        &self.dependencies
    }

    pub fn state(&self) -> &S {
        &self.state
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct MemoizationProblem<S> {
    nodes: Vec<MemoNode<S>>,
    result_id: String,
}

impl<S> MemoizationProblem<S> {
    pub fn new(
        nodes: Vec<MemoNode<S>>,
        result_id: impl Into<String>,
    ) -> Result<Self, StructureError> {
        if nodes.is_empty() {
            return Err(StructureError::new(
                "memoization requires at least one state",
            ));
        }
        let result_id = result_id.into();
        if result_id.is_empty() {
            return Err(StructureError::new(
                "memoization result ID must be nonempty",
            ));
        }
        Ok(Self { nodes, result_id })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MemoizationControl {
    None,
    BypassRegistry,
    BypassTraversal,
    BypassReduction,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct MemoizationResult<V> {
    pub result: V,
    pub admitted_states: usize,
    pub stored_states: usize,
}

pub fn run_memoization<S, V>(
    problem: MemoizationProblem<S>,
    derive_candidates: impl Fn(&MemoNode<S>, &ResourceRegistry<V>) -> Result<Vec<V>, StructureError>,
    identity: V,
    combine: impl Fn(V, V) -> V,
    trace: &mut TraceLog,
    scope: &str,
    control: MemoizationControl,
) -> Result<MemoizationResult<V>, StructureError>
where
    S: Clone,
    V: Clone,
{
    let MemoizationProblem { nodes, result_id } = problem;
    let subject = memoization_subject(scope);
    let subject = subject.as_str();
    let mut detached = TraceLog::default();
    let definitions = if control == MemoizationControl::BypassRegistry {
        ResourceRegistry::build(
            nodes.into_iter().map(|node| (node.id().to_string(), node)),
            &mut detached,
            subject,
        )?
    } else {
        ResourceRegistry::build(
            nodes.into_iter().map(|node| (node.id().to_string(), node)),
            trace,
            subject,
        )?
    };
    if definitions.get(&result_id).is_none() {
        return Err(StructureError::new(format!(
            "memoization result ID {result_id} is absent"
        )));
    }
    for id in definitions.ids() {
        let node = definitions
            .get(id)
            .expect("resource registry returned its own ID");
        for dependency in node.dependencies() {
            if definitions.get(dependency).is_none() {
                return Err(StructureError::new(format!(
                    "memoization node {id} depends on missing state {dependency}"
                )));
            }
        }
    }

    let mut values = if control == MemoizationControl::BypassRegistry {
        ResourceRegistry::empty(&mut detached, subject)
    } else {
        ResourceRegistry::empty(trace, subject)
    };
    let compute = |id: &str,
                   values: &mut ResourceRegistry<V>,
                   trace: &mut TraceLog,
                   detached: &mut TraceLog|
     -> Result<(), StructureError> {
        let node = definitions
            .get(id)
            .ok_or_else(|| StructureError::new(format!("unknown memoization state {id}")))?;
        let candidates = derive_candidates(node, values)?;
        if candidates.is_empty() {
            return Err(StructureError::new(format!(
                "memoization state {id} produced no reduction candidates"
            )));
        }
        let value = if control == MemoizationControl::BypassReduction {
            candidates.into_iter().fold(identity.clone(), &combine)
        } else {
            Reduction::fold(candidates, identity.clone(), &combine, trace, subject)
        };
        if control == MemoizationControl::BypassRegistry {
            values.insert(id.to_string(), value, detached, subject)
        } else {
            values.insert(id.to_string(), value, trace, subject)
        }
    };

    if control == MemoizationControl::BypassTraversal {
        let mut remaining: BTreeSet<String> = definitions.ids().cloned().collect();
        while !remaining.is_empty() {
            let ready: Vec<String> = remaining
                .iter()
                .filter(|id| {
                    definitions
                        .get(id)
                        .expect("registered memoization node")
                        .dependencies()
                        .iter()
                        .all(|dependency| values.contains(dependency))
                })
                .cloned()
                .collect();
            if ready.is_empty() {
                return Err(StructureError::new(
                    "memoization dependency graph contains a cycle",
                ));
            }
            for id in ready {
                compute(&id, &mut values, trace, &mut detached)?;
                remaining.remove(&id);
            }
        }
    } else {
        let roots: Vec<String> = definitions
            .ids()
            .filter(|id| {
                definitions
                    .get(id)
                    .expect("registered memoization node")
                    .dependencies()
                    .is_empty()
            })
            .cloned()
            .collect();
        let Some((first, rest)) = roots.split_first() else {
            return Err(StructureError::new(
                "memoization dependency graph has no root",
            ));
        };
        let mut traversal = TraversalEngine::new(first.clone(), trace, subject);
        let mut queued: BTreeSet<String> = roots.iter().cloned().collect();
        for root in rest {
            traversal.enqueue(root.clone(), trace);
        }
        while !traversal.frontier().is_empty() {
            let item = traversal.visit_at(0, trace)?;
            let work_id = item.work_id();
            let id = item.into_payload();
            compute(&id, &mut values, trace, &mut detached)?;
            traversal.accept(work_id, trace)?;
            let ready: Vec<String> = definitions
                .ids()
                .filter(|candidate| {
                    !queued.contains(*candidate)
                        && definitions
                            .get(candidate)
                            .expect("registered memoization node")
                            .dependencies()
                            .iter()
                            .all(|dependency| values.contains(dependency))
                })
                .cloned()
                .collect();
            for candidate in ready {
                queued.insert(candidate.clone());
                traversal.enqueue(candidate, trace);
            }
        }
        traversal.finish(trace)?;
    }

    if values.len() != definitions.len() {
        return Err(StructureError::new(format!(
            "memoization stored {} of {} admitted states",
            values.len(),
            definitions.len()
        )));
    }
    let result = values
        .get(&result_id)
        .ok_or_else(|| StructureError::new("memoization result was not stored"))?
        .clone();
    Ok(MemoizationResult {
        result,
        admitted_states: definitions.len(),
        stored_states: values.len(),
    })
}
