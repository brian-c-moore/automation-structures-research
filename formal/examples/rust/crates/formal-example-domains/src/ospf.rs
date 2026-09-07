use crate::{references, Check, ExampleRun};
use formal_example_structures::{
    rooted_frontier_subject, run_minimum_frontier, AllocationRecord, AllocationSnapshot,
    CompetitiveSelection, Edge, FrontierCandidate, FrontierTarget, PathReduction, QualityNode,
    RecipeEdge, RelationshipGraph, Relaxation, ResourceRegistry, RootedFrontierControl, Structure,
    StructureError, TraceLog, TraversalEngine, ROOTED_FRONTIER_EDGES, ROOTED_FRONTIER_STRUCTURES,
};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum VertexKind {
    Router,
    TransitNetwork,
    Destination,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Vertex {
    pub id: String,
    pub kind: VertexKind,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Link {
    pub from: String,
    pub to: String,
    pub cost: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct OspfInput {
    pub topology_version: u64,
    pub expected_version: u64,
    pub root: String,
    pub vertices: Vec<Vertex>,
    pub links: Vec<Link>,
    pub destinations: Vec<String>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct RouteEntry {
    pub destination: String,
    pub cost: u64,
    pub next_hops: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct OspfOutput {
    pub routes: Vec<RouteEntry>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OspfFault {
    None,
    IncreaseFirstLinkCost,
    ReverseFirstLink,
    StaleTopology,
    DropLastDestination,
    BypassFrontierDiscovery,
    BypassFrontierSelection,
    OmitFrontierSnapshotTrace,
    ReverseFrontierOrder,
    CorruptFrontierHierarchy,
    PreselectFrontierWinners,
}

#[derive(Clone, Debug)]
struct QueueEntry {
    vertex: String,
    cost: u64,
}

struct OspfComputation {
    working: OspfInput,
    routes: Vec<RouteEntry>,
    trace: TraceLog,
}

fn validate_input(input: &OspfInput) -> Result<(), StructureError> {
    if input.topology_version != input.expected_version {
        return Err(StructureError::new(format!(
            "stale link-state topology: expected version {}, observed {}",
            input.expected_version, input.topology_version
        )));
    }
    let mut ids = BTreeSet::new();
    for vertex in &input.vertices {
        if vertex.id.is_empty() || !ids.insert(&vertex.id) {
            return Err(StructureError::new(
                "OSPF vertex IDs must be nonempty and unique",
            ));
        }
    }
    if !ids.contains(&input.root) {
        return Err(StructureError::new("OSPF root is absent from the topology"));
    }
    for destination in &input.destinations {
        if destination == &input.root {
            return Err(StructureError::new(
                "OSPF destinations must exclude the root",
            ));
        }
        if !ids.contains(destination) {
            return Err(StructureError::new(format!(
                "OSPF destination {destination} is absent from the topology"
            )));
        }
    }
    let destinations: BTreeSet<_> = input.destinations.iter().collect();
    if destinations.len() != input.destinations.len() {
        return Err(StructureError::new("OSPF destinations must be unique"));
    }
    Ok(())
}

fn next_hops(
    input: &OspfInput,
    registry: &ResourceRegistry<Vertex>,
    graph: &RelationshipGraph,
    distances: &BTreeMap<String, u64>,
) -> Result<BTreeMap<String, BTreeSet<String>>, StructureError> {
    let mut hops: BTreeMap<String, BTreeSet<String>> = input
        .vertices
        .iter()
        .map(|vertex| (vertex.id.clone(), BTreeSet::new()))
        .collect();
    for _ in 0..input.vertices.len() {
        let mut changed = false;
        for edge in graph.edges() {
            if edge.to == input.root {
                continue;
            }
            let Some(from_distance) = distances.get(&edge.from) else {
                continue;
            };
            let Some(to_distance) = distances.get(&edge.to) else {
                continue;
            };
            if from_distance.checked_add(edge.weight) != Some(*to_distance) {
                continue;
            }
            let candidates = if edge.from == input.root {
                let target = registry.get(&edge.to).ok_or_else(|| {
                    StructureError::new(format!("missing registered vertex {}", edge.to))
                })?;
                let mut first = BTreeSet::new();
                first.insert(if target.kind == VertexKind::Router {
                    target.id.clone()
                } else {
                    "*".to_string()
                });
                first
            } else {
                hops.get(&edge.from).cloned().unwrap_or_default()
            };
            let target = hops
                .get_mut(&edge.to)
                .ok_or_else(|| StructureError::new("next-hop target is not registered"))?;
            let prior = target.len();
            target.extend(candidates);
            changed |= target.len() != prior;
        }
        if !changed {
            break;
        }
    }
    Ok(hops)
}

const CONVENTIONAL_STRUCTURES: [Structure; 6] = [
    Structure::ResourceRegistry,
    Structure::RelationshipGraph,
    Structure::TraversalEngine,
    Structure::CompetitiveSelection,
    Structure::Reduction,
    Structure::AllocationSnapshot,
];

const CONVENTIONAL_EDGES: [RecipeEdge; 3] = [
    RecipeEdge {
        before: Structure::ResourceRegistry,
        before_action: "Commit",
        after: Structure::RelationshipGraph,
        after_action: "Commit",
    },
    RecipeEdge {
        before: Structure::RelationshipGraph,
        before_action: "Commit",
        after: Structure::TraversalEngine,
        after_action: "Complete",
    },
    RecipeEdge {
        before: Structure::TraversalEngine,
        before_action: "Complete",
        after: Structure::AllocationSnapshot,
        after_action: "Commit",
    },
];

fn conventional_subject(scenario: &str) -> String {
    format!("{scenario}::conventional-spf")
}

fn compute_ospf(
    scenario: &str,
    input: &OspfInput,
    fault: OspfFault,
) -> Result<OspfComputation, StructureError> {
    let mut working = input.clone();
    if fault == OspfFault::StaleTopology {
        working.topology_version = working.topology_version.saturating_sub(1);
    }
    validate_input(&working)?;
    if let Some(first) = working.links.first_mut() {
        match fault {
            OspfFault::IncreaseFirstLinkCost => {
                first.cost = first
                    .cost
                    .checked_add(1)
                    .ok_or_else(|| StructureError::new("mutated link cost overflow"))?;
            }
            OspfFault::ReverseFirstLink => {
                std::mem::swap(&mut first.from, &mut first.to);
            }
            _ => {}
        }
    }

    let subject = conventional_subject(scenario);
    let mut trace = TraceLog::default();
    let registry = ResourceRegistry::build(
        working
            .vertices
            .iter()
            .cloned()
            .map(|vertex| (vertex.id.clone(), vertex)),
        &mut trace,
        &subject,
    )?;
    let graph = RelationshipGraph::build(
        registry.ids().cloned(),
        working
            .links
            .iter()
            .map(|link| Edge {
                from: link.from.clone(),
                to: link.to.clone(),
                weight: link.cost,
            })
            .collect(),
        &mut trace,
        &subject,
    )?;
    if !graph.contains_vertex(&working.root) {
        return Err(StructureError::new("relationship graph lost the OSPF root"));
    }

    let mut distances = BTreeMap::new();
    distances.insert(working.root.clone(), 0u64);
    let root = QueueEntry {
        vertex: working.root.clone(),
        cost: 0,
    };
    let mut traversal = TraversalEngine::new(root, &mut trace, &subject);
    let mut settled = BTreeSet::new();

    while !traversal.frontier().is_empty() {
        let index = CompetitiveSelection::select_min_index(
            traversal.frontier(),
            |item| {
                (
                    item.payload().cost,
                    item.payload().vertex.clone(),
                    item.work_id(),
                )
            },
            &mut trace,
            &subject,
        )?;
        let item = traversal.visit_at(index, &mut trace)?;
        let work_id = item.work_id();
        let entry = item.into_payload();
        traversal.accept(work_id, &mut trace)?;
        if distances.get(&entry.vertex) != Some(&entry.cost)
            || !settled.insert(entry.vertex.clone())
        {
            continue;
        }
        for edge in graph.outgoing(&entry.vertex) {
            let candidate = entry
                .cost
                .checked_add(edge.weight)
                .ok_or_else(|| StructureError::new("OSPF path cost overflow"))?;
            match PathReduction::compare(
                distances.get(&edge.to).copied(),
                candidate,
                &mut trace,
                &subject,
            ) {
                Relaxation::Install | Relaxation::Replace => {
                    distances.insert(edge.to.clone(), candidate);
                    traversal.enqueue(
                        QueueEntry {
                            vertex: edge.to.clone(),
                            cost: candidate,
                        },
                        &mut trace,
                    );
                }
                Relaxation::Equal | Relaxation::Reject => {}
            }
        }
    }
    traversal.finish(&mut trace)?;

    let hops = next_hops(&working, &registry, &graph, &distances)?;
    let mut routes = Vec::new();
    for destination in &working.destinations {
        let Some(cost) = distances.get(destination) else {
            continue;
        };
        let next_hops: Vec<String> = hops
            .get(destination)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .collect();
        routes.push(RouteEntry {
            destination: destination.clone(),
            cost: *cost,
            next_hops,
        });
    }
    routes.sort();
    if fault == OspfFault::DropLastDestination {
        routes.pop();
    }
    Ok(OspfComputation {
        working,
        routes,
        trace,
    })
}

fn commit_conventional(
    computation: &mut OspfComputation,
    scenario: &str,
) -> Result<OspfOutput, StructureError> {
    let subject = conventional_subject(scenario);
    let snapshot = AllocationSnapshot::committed(
        computation
            .routes
            .iter()
            .cloned()
            .map(|route| AllocationRecord {
                id: route.destination.clone(),
                cost: route.cost,
                value: route,
            })
            .collect(),
        &mut computation.trace,
        &subject,
    )?;
    Ok(OspfOutput {
        routes: snapshot
            .records()
            .iter()
            .map(|record| record.value.clone())
            .collect(),
    })
}

fn conventional_recipe(trace: &TraceLog, scenario: &str) -> Result<(), StructureError> {
    trace.verify_recipe_for(
        &conventional_subject(scenario),
        &CONVENTIONAL_STRUCTURES,
        &CONVENTIONAL_EDGES,
    )
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RouteCandidate {
    cost: u64,
    next_hop: String,
    path: Vec<String>,
}

#[derive(Clone)]
struct PathState {
    node_id: String,
    parent_id: Option<String>,
    path: Vec<String>,
    cost: u64,
}

fn candidate_source_subject(scenario: &str) -> String {
    format!("{scenario}::candidate-source")
}

fn path_node_id(path: &[String]) -> String {
    path.iter()
        .map(|part| format!("{}:{part}", part.len()))
        .collect::<Vec<_>>()
        .join("|")
}

fn enumerate_route_frontier(
    input: &OspfInput,
    trace: &mut TraceLog,
    scenario: &str,
    corrupt_hierarchy: bool,
) -> Result<(Vec<QualityNode>, Vec<FrontierTarget<RouteCandidate>>), StructureError> {
    let subject = candidate_source_subject(scenario);
    let registry = ResourceRegistry::build(
        input
            .vertices
            .iter()
            .cloned()
            .map(|vertex| (vertex.id.clone(), vertex)),
        trace,
        &subject,
    )?;
    let graph = RelationshipGraph::build(
        registry.ids().cloned(),
        input
            .links
            .iter()
            .map(|link| Edge {
                from: link.from.clone(),
                to: link.to.clone(),
                weight: link.cost,
            })
            .collect(),
        trace,
        &subject,
    )?;

    let root_path = vec![input.root.clone()];
    let mut stack = vec![PathState {
        node_id: path_node_id(&root_path),
        parent_id: None,
        path: root_path,
        cost: 0,
    }];
    let destinations: BTreeSet<_> = input.destinations.iter().cloned().collect();
    let mut candidates: BTreeMap<String, Vec<FrontierCandidate<RouteCandidate>>> = input
        .destinations
        .iter()
        .cloned()
        .map(|destination| (destination, Vec::new()))
        .collect();
    let mut nodes = Vec::new();
    while let Some(state) = stack.pop() {
        let depth = state.path.len().saturating_sub(1);
        let remaining = input.vertices.len().saturating_sub(depth);
        let level = u32::try_from(remaining + 1)
            .map_err(|_| StructureError::new("candidate path depth exceeds u32"))?;
        nodes.push(QualityNode {
            id: state.node_id.clone(),
            parent: state.parent_id.clone(),
            level,
            cost: state.cost,
        });

        let current = state.path.last().expect("path state is nonempty");
        if destinations.contains(current) {
            let next_hop = match state.path.get(1) {
                None => "*".to_string(),
                Some(first) => {
                    let vertex = registry.get(first).ok_or_else(|| {
                        StructureError::new(format!("missing registered vertex {first}"))
                    })?;
                    if vertex.kind == VertexKind::Router {
                        first.clone()
                    } else {
                        "*".to_string()
                    }
                }
            };
            candidates
                .get_mut(current)
                .expect("declared destination has a candidate bucket")
                .push(FrontierCandidate {
                    node_id: state.node_id.clone(),
                    record: AllocationRecord {
                        id: current.clone(),
                        cost: state.cost,
                        value: RouteCandidate {
                            cost: state.cost,
                            next_hop,
                            path: state.path.clone(),
                        },
                    },
                });
        }

        for edge in graph.outgoing(current).iter().rev() {
            if state.path.contains(&edge.to) {
                continue;
            }
            let cost = state
                .cost
                .checked_add(edge.weight)
                .ok_or_else(|| StructureError::new("candidate path cost overflow"))?;
            let mut path = state.path.clone();
            path.push(edge.to.clone());
            stack.push(PathState {
                node_id: path_node_id(&path),
                parent_id: Some(state.node_id.clone()),
                path,
                cost,
            });
        }
    }

    if corrupt_hierarchy {
        let levels: BTreeMap<_, _> = nodes
            .iter()
            .map(|node| (node.id.clone(), node.level))
            .collect();
        if let Some(node) = nodes.iter_mut().find(|node| node.parent.is_some()) {
            node.level = levels[node.parent.as_ref().expect("selected child")];
        }
    }
    let targets = input
        .destinations
        .iter()
        .map(|destination| {
            let candidates = candidates
                .remove(destination)
                .expect("declared destination has a candidate bucket");
            FrontierTarget {
                id: destination.clone(),
                candidates,
            }
        })
        .collect();
    Ok((nodes, targets))
}

fn project_route(
    destination: &str,
    candidates: &[&FrontierCandidate<RouteCandidate>],
) -> Result<AllocationRecord<RouteEntry>, StructureError> {
    let first = candidates
        .first()
        .ok_or_else(|| StructureError::new("route projection has no selected candidate"))?;
    let cost = first.record.value.cost;
    let mut next_hops = BTreeSet::new();
    for candidate in candidates {
        if candidate.record.value.cost != cost {
            return Err(StructureError::new(
                "route projection received candidates with unequal measures",
            ));
        }
        if candidate.record.value.path.first().map(String::as_str) == Some(destination) {
            next_hops.insert("*".to_string());
        } else {
            next_hops.insert(candidate.record.value.next_hop.clone());
        }
    }
    let route = RouteEntry {
        destination: destination.to_string(),
        cost,
        next_hops: next_hops.into_iter().collect(),
    };
    Ok(AllocationRecord {
        id: destination.to_string(),
        cost,
        value: route,
    })
}

fn retain_conventional_winners(
    targets: &mut [FrontierTarget<RouteCandidate>],
    routes: &[RouteEntry],
) {
    let routes: BTreeMap<_, _> = routes
        .iter()
        .map(|route| (route.destination.as_str(), route))
        .collect();
    for target in targets {
        let route = routes.get(target.id.as_str());
        target.candidates.retain(|candidate| {
            route
                .map(|route| {
                    candidate.record.value.cost == route.cost
                        && route.next_hops.contains(&candidate.record.value.next_hop)
                })
                .unwrap_or(false)
        });
    }
}

pub fn run_ospf_conventional(
    scenario: &str,
    input: &OspfInput,
    fault: OspfFault,
) -> Result<ExampleRun<OspfOutput>, StructureError> {
    let mut computation = compute_ospf(scenario, input, fault)?;
    let output = commit_conventional(&mut computation, scenario)?;
    let reference = references::ospf_reference(input).map_err(StructureError::new)?;
    let recipe = conventional_recipe(&computation.trace, scenario);
    let mut checks = vec![
        Check::verdict(
            "independent-result",
            output == reference,
            "conventional structure Dijkstra equals the separate Bellman-Ford reference",
        ),
        Check::verdict(
            "recipe-binding",
            recipe.is_ok(),
            recipe
                .err()
                .map(|error| error.to_string())
                .unwrap_or_else(|| "registered structure events and edges are present".to_string()),
        ),
        Check::pass(
            "topology-freshness",
            format!(
                "accepted topology version {}",
                computation.working.topology_version
            ),
        ),
        Check::pass(
            "route-snapshot",
            format!("committed {} reachable destinations", output.routes.len()),
        ),
    ];
    if scenario == "rfc2328-rt6" {
        let expected = rfc2328_table2_expected();
        checks.push(Check::verdict(
            "rfc2328-table-2",
            output == expected,
            "local destinations match RFC 2328 Table 2",
        ));
    }
    Ok(ExampleRun {
        id: "FEX-OSPF-001".to_string(),
        scenario: scenario.to_string(),
        output,
        reference,
        checks,
        trace: computation.trace,
        residuals: vec![
            "This conventional path is preserved as a comparison implementation.".to_string(),
            "Input is a normalized directed topology, not a live LSA database.".to_string(),
            "Flooding, aging, authentication, areas, external routes, and convergence are excluded."
                .to_string(),
            "The committed route snapshot does not claim AllocationSnapshot budget semantics."
                .to_string(),
        ],
    })
}

pub fn run_ospf(
    scenario: &str,
    input: &OspfInput,
    fault: OspfFault,
) -> Result<ExampleRun<OspfOutput>, StructureError> {
    let mut computation = compute_ospf(scenario, input, fault)?;
    let conventional = commit_conventional(&mut computation, scenario)?;
    let conventional_binding = conventional_recipe(&computation.trace, scenario);

    let (hierarchy, mut targets) = enumerate_route_frontier(
        &computation.working,
        &mut computation.trace,
        scenario,
        fault == OspfFault::CorruptFrontierHierarchy,
    )?;
    let source_targets = targets.clone();
    let source_candidate_count: usize = source_targets
        .iter()
        .map(|target| target.candidates.len())
        .sum();
    if fault == OspfFault::PreselectFrontierWinners {
        retain_conventional_winners(&mut targets, &conventional.routes);
    }
    let submitted_candidate_count: usize =
        targets.iter().map(|target| target.candidates.len()).sum();
    let submitted_candidates_match_source = targets == source_targets;
    let control = match fault {
        OspfFault::BypassFrontierDiscovery => RootedFrontierControl::BypassDiscovery,
        OspfFault::BypassFrontierSelection => RootedFrontierControl::BypassSelection,
        OspfFault::OmitFrontierSnapshotTrace => RootedFrontierControl::OmitSnapshotTrace,
        _ => RootedFrontierControl::None,
    };
    let reverse_order = fault == OspfFault::ReverseFrontierOrder;
    let frontier = run_minimum_frontier(
        hierarchy,
        targets,
        |candidate| {
            if reverse_order {
                u64::MAX - candidate.record.value.cost
            } else {
                candidate.record.value.cost
            }
        },
        project_route,
        &mut computation.trace,
        scenario,
        control,
    )?;
    let mut routes: Vec<_> = frontier
        .snapshot
        .records()
        .iter()
        .map(|record| record.value.clone())
        .collect();
    routes.sort();
    let output = OspfOutput { routes };
    let reference = references::ospf_reference(input).map_err(StructureError::new)?;
    let frontier_binding = computation.trace.verify_recipe_for(
        &rooted_frontier_subject(scenario),
        &ROOTED_FRONTIER_STRUCTURES,
        &ROOTED_FRONTIER_EDGES,
    );
    let mut checks = vec![
        Check::verdict(
            "conventional-independent-result",
            conventional == reference,
            "conventional structure Dijkstra equals the separate Bellman-Ford reference",
        ),
        Check::verdict(
            "shared-frontier-independent-result",
            output == reference,
            "shared rooted-frontier selection equals the separate Bellman-Ford reference",
        ),
        Check::verdict(
            "shared-frontier-conventional-agreement",
            output == conventional,
            "shared rooted-frontier and conventional Dijkstra paths commit the same routing table",
        ),
        Check::verdict(
            "candidate-input-unchanged",
            submitted_candidates_match_source,
            format!(
                "source_candidates={source_candidate_count} submitted_candidates={submitted_candidate_count}"
            ),
        ),
        Check::verdict(
            "conventional-recipe-binding",
            conventional_binding.is_ok(),
            conventional_binding
                .err()
                .map(|error| error.to_string())
                .unwrap_or_else(|| "conventional OSPF recipe is present".to_string()),
        ),
        Check::verdict(
            "shared-frontier-recipe-binding",
            frontier_binding.is_ok(),
            frontier_binding
                .err()
                .map(|error| error.to_string())
                .unwrap_or_else(|| "shared rooted-frontier recipe is present".to_string()),
        ),
        Check::pass(
            "shared-frontier-selection",
            format!(
                "selected {} of {} path candidates from {} hierarchy nodes",
                frontier.selected_candidates, frontier.candidate_count, frontier.hierarchy_nodes
            ),
        ),
        Check::pass(
            "topology-freshness",
            format!(
                "accepted topology version {}",
                computation.working.topology_version
            ),
        ),
        Check::pass(
            "route-snapshot",
            format!("committed {} reachable destinations", output.routes.len()),
        ),
    ];
    if scenario == "rfc2328-rt6" {
        let expected = rfc2328_table2_expected();
        checks.push(Check::verdict(
            "rfc2328-table-2",
            output == expected,
            "shared path local destinations match RFC 2328 Table 2",
        ));
    }
    Ok(ExampleRun {
        id: "FEX-OSPF-001".to_string(),
        scenario: scenario.to_string(),
        output,
        reference,
        checks,
        trace: computation.trace,
        residuals: vec![
            "The conventional Dijkstra composition remains present as a comparison path."
                .to_string(),
            "The shared rooted-frontier path enumerates finite simple-path candidates before selecting minimum measures and declared ties."
                .to_string(),
            "Exhaustive candidate enumeration is bounded construction evidence, not a production routing-performance claim."
                .to_string(),
            "Input is a normalized directed topology, not a live LSA database.".to_string(),
            "Flooding, aging, authentication, areas, external routes, and convergence are excluded."
                .to_string(),
        ],
    })
}

fn vertex(id: &str, kind: VertexKind) -> Vertex {
    Vertex {
        id: id.to_string(),
        kind,
    }
}

fn link(from: &str, to: &str, cost: u64) -> Link {
    Link {
        from: from.to_string(),
        to: to.to_string(),
        cost,
    }
}

pub fn rfc2328_rt6_input() -> OspfInput {
    let mut vertices: Vec<Vertex> = (1..=12)
        .map(|index| vertex(&format!("RT{index}"), VertexKind::Router))
        .collect();
    for id in ["N3", "N6", "N8", "N9"] {
        vertices.push(vertex(id, VertexKind::TransitNetwork));
    }
    for id in ["N1", "N2", "N4", "N7", "N10", "N11", "Ia", "Ib", "H1"] {
        vertices.push(vertex(id, VertexKind::Destination));
    }
    let links = vec![
        link("RT1", "N3", 1),
        link("RT1", "N1", 3),
        link("RT2", "N3", 1),
        link("RT2", "N2", 3),
        link("RT3", "N3", 1),
        link("RT3", "RT6", 8),
        link("RT3", "N4", 2),
        link("RT4", "N3", 1),
        link("RT4", "RT5", 8),
        link("RT5", "RT4", 8),
        link("RT5", "RT6", 7),
        link("RT5", "RT7", 6),
        link("RT6", "RT3", 6),
        link("RT6", "RT5", 6),
        link("RT6", "RT10", 7),
        link("RT6", "Ib", 7),
        link("RT7", "RT5", 6),
        link("RT7", "N6", 1),
        link("RT8", "N6", 1),
        link("RT8", "N7", 4),
        link("RT9", "N9", 1),
        link("RT9", "N11", 3),
        link("RT10", "RT6", 5),
        link("RT10", "N6", 1),
        link("RT10", "N8", 3),
        link("RT10", "Ia", 5),
        link("RT11", "N8", 2),
        link("RT11", "N9", 1),
        link("RT12", "N9", 1),
        link("RT12", "N10", 2),
        link("RT12", "H1", 10),
        link("N3", "RT1", 0),
        link("N3", "RT2", 0),
        link("N3", "RT3", 0),
        link("N3", "RT4", 0),
        link("N6", "RT7", 0),
        link("N6", "RT8", 0),
        link("N6", "RT10", 0),
        link("N8", "RT10", 0),
        link("N8", "RT11", 0),
        link("N9", "RT9", 0),
        link("N9", "RT11", 0),
        link("N9", "RT12", 0),
    ];
    OspfInput {
        topology_version: 1,
        expected_version: 1,
        root: "RT6".to_string(),
        vertices,
        links,
        destinations: [
            "N1", "N2", "N3", "N4", "Ib", "Ia", "N6", "N7", "N8", "N9", "N10", "N11", "H1", "RT5",
            "RT7",
        ]
        .into_iter()
        .map(str::to_string)
        .collect(),
    }
}

pub fn rfc2328_table2_expected() -> OspfOutput {
    let mut routes = vec![
        route("N1", 10, &["RT3"]),
        route("N2", 10, &["RT3"]),
        route("N3", 7, &["RT3"]),
        route("N4", 8, &["RT3"]),
        route("Ib", 7, &["*"]),
        route("Ia", 12, &["RT10"]),
        route("N6", 8, &["RT10"]),
        route("N7", 12, &["RT10"]),
        route("N8", 10, &["RT10"]),
        route("N9", 11, &["RT10"]),
        route("N10", 13, &["RT10"]),
        route("N11", 14, &["RT10"]),
        route("H1", 21, &["RT10"]),
        route("RT5", 6, &["RT5"]),
        route("RT7", 8, &["RT10"]),
    ];
    routes.sort();
    OspfOutput { routes }
}

fn route(destination: &str, cost: u64, hops: &[&str]) -> RouteEntry {
    RouteEntry {
        destination: destination.to_string(),
        cost,
        next_hops: hops.iter().map(|hop| (*hop).to_string()).collect(),
    }
}

fn synthetic(unique_direct_cost: u64, version: u64) -> OspfInput {
    OspfInput {
        topology_version: version,
        expected_version: version,
        root: "R1".to_string(),
        vertices: vec![
            vertex("R1", VertexKind::Router),
            vertex("R2", VertexKind::Router),
            vertex("R3", VertexKind::Router),
            vertex("10.0.3.0/24", VertexKind::Destination),
        ],
        links: vec![
            link("R1", "R2", 10),
            link("R2", "R1", 10),
            link("R1", "R3", unique_direct_cost),
            link("R3", "R1", unique_direct_cost),
            link("R2", "R3", 5),
            link("R3", "R2", 5),
            link("R3", "10.0.3.0/24", 2),
        ],
        destinations: vec!["10.0.3.0/24".to_string()],
    }
}

pub fn scenarios() -> Vec<(&'static str, OspfInput)> {
    let ecmp = OspfInput {
        topology_version: 1,
        expected_version: 1,
        root: "R1".to_string(),
        vertices: vec![
            vertex("R1", VertexKind::Router),
            vertex("R2", VertexKind::Router),
            vertex("R3", VertexKind::Router),
            vertex("R4", VertexKind::Router),
            vertex("10.0.4.0/24", VertexKind::Destination),
        ],
        links: vec![
            link("R1", "R2", 10),
            link("R1", "R3", 10),
            link("R2", "R4", 5),
            link("R3", "R4", 5),
            link("R4", "10.0.4.0/24", 1),
        ],
        destinations: vec!["10.0.4.0/24".to_string()],
    };
    let unreachable = OspfInput {
        topology_version: 1,
        expected_version: 1,
        root: "R1".to_string(),
        vertices: vec![
            vertex("R1", VertexKind::Router),
            vertex("R2", VertexKind::Router),
            vertex("R5", VertexKind::Router),
            vertex("10.0.5.0/24", VertexKind::Destination),
        ],
        links: vec![link("R1", "R2", 2), link("R5", "10.0.5.0/24", 1)],
        destinations: vec!["10.0.5.0/24".to_string()],
    };
    vec![
        ("rfc2328-rt6", rfc2328_rt6_input()),
        ("unique-shortest", synthetic(30, 1)),
        ("equal-cost-next-hops", ecmp),
        ("unreachable-subnet", unreachable),
        ("topology-update", synthetic(4, 2)),
    ]
}

pub fn scenario(name: &str) -> Option<OspfInput> {
    scenarios()
        .into_iter()
        .find(|(scenario, _)| *scenario == name)
        .map(|(_, input)| input)
}

#[cfg(test)]
pub(crate) fn generated_input(seed: u64) -> OspfInput {
    let nodes = (seed % 5 + 3) as usize;
    let mut vertices: Vec<Vertex> = (0..nodes)
        .map(|index| vertex(&format!("R{index}"), VertexKind::Router))
        .collect();
    vertices.push(vertex("D", VertexKind::Destination));
    let mut links = Vec::new();
    let mut state = seed.wrapping_add(1);
    let mut next = || {
        state = state
            .wrapping_mul(2862933555777941757)
            .wrapping_add(3037000493);
        state
    };
    for from in 0..nodes.saturating_sub(1) {
        links.push(link(
            &format!("R{from}"),
            &format!("R{}", from + 1),
            next() % 9 + 1,
        ));
    }
    for from in 0..nodes {
        for to in 0..nodes {
            if from != to && to != from + 1 && next() % 4 == 0 {
                links.push(link(&format!("R{from}"), &format!("R{to}"), next() % 9 + 1));
            }
        }
    }
    links.push(link(&format!("R{}", nodes - 1), "D", next() % 5 + 1));
    OspfInput {
        topology_version: 1,
        expected_version: 1,
        root: "R0".to_string(),
        vertices,
        links,
        destinations: vec!["D".to_string()],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn published_and_bounded_scenarios_match() {
        for (name, input) in scenarios() {
            let run = run_ospf(name, &input, OspfFault::None).expect("valid OSPF fixture");
            assert!(run.passed(), "{name}: {:#?}", run.checks);
        }
    }

    #[test]
    fn generated_topologies_match_bellman_ford() {
        for seed in 0..96 {
            let input = generated_input(seed);
            let run = run_ospf(&format!("generated-{seed}"), &input, OspfFault::None)
                .expect("valid generated topology");
            assert!(run.passed(), "seed {seed}: {:#?}", run.checks);
        }
    }

    #[test]
    fn equal_cost_next_hops_are_preserved() {
        let input = scenario("equal-cost-next-hops").expect("built-in scenario");
        let run = run_ospf("equal-cost-next-hops", &input, OspfFault::None).expect("run");
        assert_eq!(run.output.routes[0].next_hops, vec!["R2", "R3"]);
        let subject = rooted_frontier_subject("equal-cost-next-hops");
        assert!(run.trace.events().iter().any(|event| {
            event.subject == subject
                && event.structure == Structure::CompetitiveSelection
                && event.action == "Commit"
                && event.detail == "winners=2"
        }));
    }

    #[test]
    fn root_is_rejected_as_a_destination() {
        let mut input = scenario("unique-shortest").expect("built-in scenario");
        input.destinations.push(input.root.clone());
        let error = run_ospf("root-destination", &input, OspfFault::None)
            .expect_err("root destination must be rejected");
        assert_eq!(error.to_string(), "OSPF destinations must exclude the root");
    }

    #[test]
    fn controls_are_discriminating() {
        let input = scenario("unique-shortest").expect("built-in scenario");
        let cost = run_ospf("unique-shortest", &input, OspfFault::IncreaseFirstLinkCost)
            .expect("cost mutation remains executable");
        assert!(!cost.passed());
        assert!(run_ospf("unique-shortest", &input, OspfFault::ReverseFirstLink).is_err());

        let update = scenario("topology-update").expect("built-in scenario");
        let stale = run_ospf("topology-update", &update, OspfFault::StaleTopology);
        assert!(stale.is_err());
        assert!(stale
            .unwrap_err()
            .message()
            .contains("stale link-state topology"));

        let coverage = run_ospf("unique-shortest", &input, OspfFault::DropLastDestination)
            .expect("coverage mutation remains executable");
        assert!(!coverage.passed());
        assert_eq!(coverage.output, coverage.reference);
        assert!(coverage
            .checks
            .iter()
            .any(|check| check.name == "conventional-independent-result" && !check.passed));
        assert!(coverage
            .checks
            .iter()
            .any(|check| check.name == "shared-frontier-independent-result" && check.passed));

        let baseline = run_ospf("unique-shortest", &input, OspfFault::None).expect("baseline");
        assert!(baseline.passed());
    }

    #[test]
    fn shared_frontier_selects_routes_and_conventional_path_is_preserved() {
        let input = scenario("unique-shortest").expect("built-in scenario");
        let conventional = run_ospf_conventional(
            "unique-shortest",
            &input,
            OspfFault::CorruptFrontierHierarchy,
        )
        .expect("frontier fault does not alter conventional SPF");
        assert!(conventional.passed());

        let undiscovered = run_ospf(
            "unique-shortest",
            &input,
            OspfFault::BypassFrontierDiscovery,
        )
        .expect("discovery bypass still computes a route result");
        assert_eq!(undiscovered.output, undiscovered.reference);
        assert!(!undiscovered.passed());
        assert!(undiscovered
            .checks
            .iter()
            .any(|check| check.name == "shared-frontier-recipe-binding" && !check.passed));

        let unselected = run_ospf(
            "unique-shortest",
            &input,
            OspfFault::BypassFrontierSelection,
        )
        .expect("selection bypass still computes a route result");
        assert!(!unselected.passed());
        assert!(unselected
            .checks
            .iter()
            .any(|check| check.name == "shared-frontier-recipe-binding" && !check.passed));
        assert!(unselected
            .checks
            .iter()
            .any(|check| check.name == "conventional-independent-result" && check.passed));

        let detached = run_ospf(
            "unique-shortest",
            &input,
            OspfFault::OmitFrontierSnapshotTrace,
        )
        .expect("detached frontier still computes the domain result");
        assert_eq!(detached.output, detached.reference);
        assert!(!detached.passed());
        assert!(detached
            .checks
            .iter()
            .any(|check| check.name == "shared-frontier-recipe-binding" && !check.passed));

        let reversed = run_ospf("unique-shortest", &input, OspfFault::ReverseFrontierOrder)
            .expect("reversed frontier policy remains executable");
        assert_ne!(reversed.output, reversed.reference);
        assert!(!reversed.passed());
        assert!(reversed
            .checks
            .iter()
            .any(|check| check.name == "conventional-independent-result" && check.passed));

        let preselected = run_ospf(
            "unique-shortest",
            &input,
            OspfFault::PreselectFrontierWinners,
        )
        .expect("preselected winners still compute the expected domain result");
        assert_eq!(preselected.output, preselected.reference);
        assert!(!preselected.passed());
        assert!(preselected
            .checks
            .iter()
            .any(|check| check.name == "candidate-input-unchanged" && !check.passed));

        let corrupt = run_ospf(
            "unique-shortest",
            &input,
            OspfFault::CorruptFrontierHierarchy,
        )
        .expect_err("invalid route hierarchy must be rejected");
        assert!(corrupt.message().contains("does not strictly descend"));
    }

    #[test]
    fn topology_update_changes_the_selected_route() {
        let before_input = scenario("unique-shortest").expect("built-in scenario");
        let after_input = scenario("topology-update").expect("built-in scenario");
        let before = run_ospf("unique-shortest", &before_input, OspfFault::None).expect("before");
        let after = run_ospf("topology-update", &after_input, OspfFault::None).expect("after");
        assert_ne!(before.output, after.output);
        assert_eq!(after.output.routes[0].next_hops, vec!["R3"]);
    }
}
