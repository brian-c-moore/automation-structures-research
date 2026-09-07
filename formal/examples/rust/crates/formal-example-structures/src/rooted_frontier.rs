use crate::{
    AllocationRecord, AllocationSnapshot, Budget, CompetitiveSelection, QualityHierarchy,
    QualityNode, RecipeEdge, Structure, StructureError, TraceLog, TraversalEngine, Unit,
};
use serde::Serialize;
use std::collections::BTreeSet;

pub const ROOTED_FRONTIER_STRUCTURES: [Structure; 4] = [
    Structure::QualityHierarchy,
    Structure::TraversalEngine,
    Structure::CompetitiveSelection,
    Structure::AllocationSnapshot,
];

pub const ROOTED_FRONTIER_EDGES: [RecipeEdge; 3] = [
    RecipeEdge {
        before: Structure::QualityHierarchy,
        before_action: "Commit",
        after: Structure::TraversalEngine,
        after_action: "Complete",
    },
    RecipeEdge {
        before: Structure::TraversalEngine,
        before_action: "Complete",
        after: Structure::CompetitiveSelection,
        after_action: "Commit",
    },
    RecipeEdge {
        before: Structure::CompetitiveSelection,
        before_action: "Commit",
        after: Structure::AllocationSnapshot,
        after_action: "Commit",
    },
];

pub const BOUNDED_FRONTIER_STRUCTURES: [Structure; 5] = [
    Structure::QualityHierarchy,
    Structure::Budget,
    Structure::TraversalEngine,
    Structure::CompetitiveSelection,
    Structure::AllocationSnapshot,
];

pub const BOUNDED_FRONTIER_EDGES: [RecipeEdge; 5] = [
    ROOTED_FRONTIER_EDGES[0],
    RecipeEdge {
        before: Structure::QualityHierarchy,
        before_action: "Commit",
        after: Structure::Budget,
        after_action: "Initialize",
    },
    RecipeEdge {
        before: Structure::Budget,
        before_action: "Initialize",
        after: Structure::Budget,
        after_action: "Check",
    },
    ROOTED_FRONTIER_EDGES[1],
    ROOTED_FRONTIER_EDGES[2],
];

pub fn rooted_frontier_subject(scope: &str) -> String {
    format!("{scope}::rooted-frontier-selection")
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct FrontierCandidate<T> {
    pub node_id: String,
    pub record: AllocationRecord<T>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct FrontierTarget<T> {
    pub id: String,
    pub candidates: Vec<FrontierCandidate<T>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BoundedFrontierControl {
    None,
    BypassDiscovery,
    BypassSelection,
    SkipBudgetCharge,
    OmitSnapshotTrace,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RootedFrontierControl {
    None,
    BypassDiscovery,
    BypassSelection,
    OmitSnapshotTrace,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct BoundedFrontierResult<T> {
    pub snapshot: AllocationSnapshot<T>,
    pub hierarchy_nodes: usize,
    pub candidate_count: usize,
    pub complete_plans: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct MinimumFrontierResult<T> {
    pub snapshot: AllocationSnapshot<T>,
    pub hierarchy_nodes: usize,
    pub candidate_count: usize,
    pub selected_candidates: usize,
}

struct DiscoveredFrontier<T> {
    targets: Vec<FrontierTarget<T>>,
    hierarchy_nodes: usize,
    candidate_count: usize,
}

fn discover_frontier<T>(
    hierarchy_nodes: Vec<QualityNode>,
    targets: Vec<FrontierTarget<T>>,
    trace: &mut TraceLog,
    subject: &str,
) -> Result<DiscoveredFrontier<T>, StructureError> {
    let hierarchy = QualityHierarchy::build(hierarchy_nodes, trace, subject)?;
    let roots = hierarchy.roots();
    if !hierarchy.is_empty() && roots.is_empty() {
        return Err(StructureError::new("quality hierarchy has no root"));
    }

    let mut discovered = BTreeSet::new();
    if let Some((first, remaining)) = roots.split_first() {
        let mut traversal = TraversalEngine::new(first.clone(), trace, subject);
        for root in remaining {
            traversal.enqueue(root.clone(), trace);
        }
        while !traversal.frontier().is_empty() {
            let index = traversal.frontier().len() - 1;
            let item = traversal.visit_at(index, trace)?;
            let work_id = item.work_id();
            let node_id = item.into_payload();
            if !discovered.insert(node_id.clone()) {
                return Err(StructureError::new(format!(
                    "hierarchy traversal reached node {node_id} twice"
                )));
            }
            for child in hierarchy.children(&node_id) {
                traversal.enqueue(child, trace);
            }
            traversal.accept(work_id, trace)?;
        }
        traversal.finish(trace)?;
    }
    if discovered.len() != hierarchy.len() {
        return Err(StructureError::new(format!(
            "hierarchy traversal discovered {} of {} nodes",
            discovered.len(),
            hierarchy.len()
        )));
    }

    let mut target_ids = BTreeSet::new();
    let mut candidate_nodes = BTreeSet::new();
    let mut candidate_count = 0usize;
    for target in &targets {
        if target.id.is_empty() || !target_ids.insert(&target.id) {
            return Err(StructureError::new(
                "frontier target IDs must be nonempty and unique",
            ));
        }
        for candidate in &target.candidates {
            if candidate.record.id != target.id {
                return Err(StructureError::new(format!(
                    "frontier target {} contains a record for {}",
                    target.id, candidate.record.id
                )));
            }
            if !candidate_nodes.insert(&candidate.node_id) {
                return Err(StructureError::new(format!(
                    "frontier candidate node {} is duplicated",
                    candidate.node_id
                )));
            }
            if !discovered.contains(&candidate.node_id) {
                return Err(StructureError::new(format!(
                    "frontier candidate node {} was not reached through the hierarchy",
                    candidate.node_id
                )));
            }
            candidate_count += 1;
        }
    }

    Ok(DiscoveredFrontier {
        targets,
        hierarchy_nodes: hierarchy.len(),
        candidate_count,
    })
}

#[derive(Clone)]
struct PlanState<T, U: Unit> {
    target_index: usize,
    records: Vec<AllocationRecord<T>>,
    budget: Budget<U>,
}

pub fn run_bounded_frontier<U, T, K>(
    hierarchy_nodes: Vec<QualityNode>,
    targets: Vec<FrontierTarget<T>>,
    capacity: u64,
    rank_plan: impl Fn(&[AllocationRecord<T>]) -> K,
    trace: &mut TraceLog,
    scope: &str,
    control: BoundedFrontierControl,
) -> Result<BoundedFrontierResult<T>, StructureError>
where
    U: Unit,
    T: Clone,
    K: Ord,
{
    let subject = rooted_frontier_subject(scope);
    let subject = subject.as_str();
    let discovered = if control == BoundedFrontierControl::BypassDiscovery {
        DiscoveredFrontier {
            candidate_count: targets.iter().map(|target| target.candidates.len()).sum(),
            targets,
            hierarchy_nodes: 0,
        }
    } else {
        discover_frontier(hierarchy_nodes, targets, trace, subject)?
    };

    let root = PlanState {
        target_index: 0,
        records: Vec::new(),
        budget: Budget::<U>::new(capacity, trace, subject),
    };
    let mut traversal = TraversalEngine::new(root, trace, subject);
    let mut plans = Vec::new();
    while !traversal.frontier().is_empty() {
        let index = traversal.frontier().len() - 1;
        let item = traversal.visit_at(index, trace)?;
        let work_id = item.work_id();
        let state = item.into_payload();
        traversal.accept(work_id, trace)?;
        if state.target_index == discovered.targets.len() {
            plans.push(state.records);
            continue;
        }

        let target = &discovered.targets[state.target_index];
        let mut skipped = state.clone();
        skipped.target_index += 1;
        traversal.enqueue(skipped, trace);
        for candidate in &target.candidates {
            let mut next = state.clone();
            next.target_index += 1;
            if control != BoundedFrontierControl::SkipBudgetCharge
                && next
                    .budget
                    .try_reserve(candidate.record.cost, trace, subject)
                    .is_err()
            {
                continue;
            }
            next.records.push(candidate.record.clone());
            traversal.enqueue(next, trace);
        }
    }
    traversal.finish(trace)?;

    let selected = if control == BoundedFrontierControl::BypassSelection {
        if plans.is_empty() {
            return Err(StructureError::new(
                "bounded frontier produced no complete plan",
            ));
        }
        0
    } else {
        CompetitiveSelection::select_min_index(&plans, |plan| rank_plan(plan), trace, subject)
            .map_err(|_| StructureError::new("bounded frontier produced no complete plan"))?
    };
    let records = plans[selected].clone();
    let snapshot = if control == BoundedFrontierControl::OmitSnapshotTrace {
        let mut detached = TraceLog::default();
        AllocationSnapshot::bounded(records, capacity, &mut detached, subject)?
    } else {
        AllocationSnapshot::bounded(records, capacity, trace, subject)?
    };
    Ok(BoundedFrontierResult {
        snapshot,
        hierarchy_nodes: discovered.hierarchy_nodes,
        candidate_count: discovered.candidate_count,
        complete_plans: plans.len(),
    })
}

pub fn run_minimum_frontier<T, O, K>(
    hierarchy_nodes: Vec<QualityNode>,
    targets: Vec<FrontierTarget<T>>,
    rank_candidate: impl Fn(&FrontierCandidate<T>) -> K,
    project_selected: impl Fn(
        &str,
        &[&FrontierCandidate<T>],
    ) -> Result<AllocationRecord<O>, StructureError>,
    trace: &mut TraceLog,
    scope: &str,
    control: RootedFrontierControl,
) -> Result<MinimumFrontierResult<O>, StructureError>
where
    K: Ord,
{
    let subject = rooted_frontier_subject(scope);
    let subject = subject.as_str();
    let discovered = if control == RootedFrontierControl::BypassDiscovery {
        DiscoveredFrontier {
            candidate_count: targets.iter().map(|target| target.candidates.len()).sum(),
            targets,
            hierarchy_nodes: 0,
        }
    } else {
        discover_frontier(hierarchy_nodes, targets, trace, subject)?
    };
    let mut records = Vec::new();
    let mut selected_candidates = 0usize;
    for target in &discovered.targets {
        let selected = if control == RootedFrontierControl::BypassSelection {
            if target.candidates.is_empty() {
                Vec::new()
            } else {
                vec![0]
            }
        } else {
            CompetitiveSelection::select_min_indices(
                &target.candidates,
                &rank_candidate,
                trace,
                subject,
            )?
        };
        if selected.is_empty() {
            continue;
        }
        let candidates: Vec<_> = selected
            .iter()
            .map(|index| &target.candidates[*index])
            .collect();
        selected_candidates += candidates.len();
        let record = project_selected(&target.id, &candidates)?;
        if record.id != target.id {
            return Err(StructureError::new(format!(
                "frontier projection for {} produced record {}",
                target.id, record.id
            )));
        }
        records.push(record);
    }
    let snapshot = if control == RootedFrontierControl::OmitSnapshotTrace {
        let mut detached = TraceLog::default();
        AllocationSnapshot::committed(records, &mut detached, subject)?
    } else {
        AllocationSnapshot::committed(records, trace, subject)?
    };
    Ok(MinimumFrontierResult {
        snapshot,
        hierarchy_nodes: discovered.hierarchy_nodes,
        candidate_count: discovered.candidate_count,
        selected_candidates,
    })
}
