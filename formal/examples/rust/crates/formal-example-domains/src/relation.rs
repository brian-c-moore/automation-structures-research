use crate::{evidence, lod::LodOutput, ospf::OspfOutput, ExampleRun};
use formal_example_structures::{
    rooted_frontier_subject, Structure, ROOTED_FRONTIER_EDGES, ROOTED_FRONTIER_STRUCTURES,
};
use serde::Serialize;
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct NodeCorrespondence {
    pub lod: Structure,
    pub ospf: Structure,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelationSpec {
    pub id: &'static str,
    pub nodes: Vec<NodeCorrespondence>,
}

impl RelationSpec {
    pub fn registered() -> Self {
        Self {
            id: "FEX-XFER-LOD-OSPF-01",
            nodes: vec![
                NodeCorrespondence {
                    lod: Structure::QualityHierarchy,
                    ospf: Structure::QualityHierarchy,
                },
                NodeCorrespondence {
                    lod: Structure::TraversalEngine,
                    ospf: Structure::TraversalEngine,
                },
                NodeCorrespondence {
                    lod: Structure::CompetitiveSelection,
                    ospf: Structure::CompetitiveSelection,
                },
                NodeCorrespondence {
                    lod: Structure::AllocationSnapshot,
                    ospf: Structure::AllocationSnapshot,
                },
            ],
        }
    }

    pub fn misregistered_control() -> Self {
        let mut spec = Self::registered();
        spec.nodes.push(NodeCorrespondence {
            lod: Structure::Budget,
            ospf: Structure::RelationshipGraph,
        });
        spec
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct RelationReport {
    pub id: String,
    pub passed: bool,
    pub shared_nodes: Vec<String>,
    pub shared_edges: Vec<String>,
    pub lod_only: Vec<String>,
    pub ospf_only: Vec<String>,
    pub errors: Vec<String>,
    pub residuals: Vec<String>,
}

fn names(values: BTreeSet<Structure>) -> Vec<String> {
    values
        .into_iter()
        .map(|structure| structure.name().to_string())
        .collect()
}

pub fn compare(
    lod: &ExampleRun<LodOutput>,
    ospf: &ExampleRun<OspfOutput>,
    spec: &RelationSpec,
) -> RelationReport {
    let expected: BTreeSet<NodeCorrespondence> =
        RelationSpec::registered().nodes.into_iter().collect();
    let declared: BTreeSet<NodeCorrespondence> = spec.nodes.iter().copied().collect();
    let lod_frontier_subject = rooted_frontier_subject(&lod.scenario);
    let ospf_frontier_subject = rooted_frontier_subject(&ospf.scenario);
    let lod_structures = lod.trace.structures_for(&lod_frontier_subject);
    let ospf_structures = ospf.trace.structures_for(&ospf_frontier_subject);
    let mut errors = Vec::new();

    if !lod.passed() {
        errors.push("LOD domain-result checks are not green".to_string());
    }
    if !ospf.passed() {
        errors.push("OSPF domain-result checks are not green".to_string());
    }
    let expected_structures: BTreeSet<_> = ROOTED_FRONTIER_STRUCTURES.into_iter().collect();
    let mut expected_lod_structures = expected_structures.clone();
    expected_lod_structures.insert(Structure::Budget);
    if lod_structures != expected_lod_structures {
        errors.push(format!(
            "LOD rooted-frontier structures differ: expected={expected_lod_structures:?} observed={lod_structures:?}"
        ));
    }
    if ospf_structures != expected_structures {
        errors.push(format!(
            "OSPF rooted-frontier structures differ: expected={expected_structures:?} observed={ospf_structures:?}"
        ));
    }
    for unexpected in declared.difference(&expected) {
        errors.push(format!(
            "undeclared correspondence {} -> {}",
            unexpected.lod.name(),
            unexpected.ospf.name()
        ));
    }
    for missing in expected.difference(&declared) {
        errors.push(format!(
            "missing correspondence {} -> {}",
            missing.lod.name(),
            missing.ospf.name()
        ));
    }
    for pair in &declared {
        if !lod_structures.contains(&pair.lod) {
            errors.push(format!("LOD trace lacks {}", pair.lod.name()));
        }
        if !ospf_structures.contains(&pair.ospf) {
            errors.push(format!("OSPF trace lacks {}", pair.ospf.name()));
        }
    }

    match evidence::describe(spec.id) {
        Ok(record) => {
            if let Some(contract) = record.record.relation {
                for pair in &declared {
                    for (member, structure) in
                        [("FEX-DOM-REN-03", pair.lod), ("FEX-OSPF-001", pair.ospf)]
                    {
                        let binding = contract.implementation_bindings.iter().find(|binding| {
                            binding.member_id == member && binding.node_id == structure.name()
                        });
                        if !matches!(binding, Some(binding) if binding.implementation_identity == structure.implementation_identity())
                        {
                            errors.push(format!(
                                "{member} lacks the registered implementation identity for {}",
                                structure.name()
                            ));
                        }
                    }
                }
            } else {
                errors.push("relation evidence lacks its executable contract".to_string());
            }
        }
        Err(error) => errors.push(format!("relation evidence is invalid: {error}")),
    }

    let mut shared_edges = Vec::new();
    for edge in ROOTED_FRONTIER_EDGES {
        let label = format!(
            "{}.{} -> {}.{}",
            edge.before.name(),
            edge.before_action,
            edge.after.name(),
            edge.after_action
        );
        let lod_order = (
            lod.trace
                .first_sequence_for(edge.before, edge.before_action, &lod_frontier_subject),
            lod.trace
                .first_sequence_for(edge.after, edge.after_action, &lod_frontier_subject),
        );
        let ospf_order = (
            ospf.trace
                .first_sequence_for(edge.before, edge.before_action, &ospf_frontier_subject),
            ospf.trace
                .first_sequence_for(edge.after, edge.after_action, &ospf_frontier_subject),
        );
        if !matches!(lod_order, (Some(left), Some(right)) if left < right) {
            errors.push(format!("LOD rooted frontier lacks {label}"));
        }
        if !matches!(ospf_order, (Some(left), Some(right)) if left < right) {
            errors.push(format!("OSPF rooted frontier lacks {label}"));
        }
        shared_edges.push(label);
    }

    let shared_lod: BTreeSet<Structure> = expected.iter().map(|pair| pair.lod).collect();
    let shared_ospf: BTreeSet<Structure> = expected.iter().map(|pair| pair.ospf).collect();
    let all_lod = lod.trace.structures();
    let all_ospf = ospf.trace.structures();
    RelationReport {
        id: spec.id.to_string(),
        passed: errors.is_empty(),
        shared_nodes: ROOTED_FRONTIER_STRUCTURES
            .into_iter()
            .map(|structure| structure.name().to_string())
            .collect(),
        shared_edges,
        lod_only: names(all_lod.difference(&shared_lod).copied().collect()),
        ospf_only: names(all_ospf.difference(&shared_ospf).copied().collect()),
        errors,
        residuals: vec![
            "LOD view scoring and OSPF path-cost semantics are not equated.".to_string(),
            "Budget<Bytes> is an LOD-only obligation; OSPF has no artificial route-slot budget."
                .to_string(),
            "LOD supplies fidelity candidates while OSPF supplies finite simple-path candidates."
                .to_string(),
            "ResourceRegistry, RelationshipGraph, and Reduction remain OSPF-only source and conventional machinery."
                .to_string(),
            "The conventional OSPF composition is retained beside the shared rooted frontier."
                .to_string(),
        ],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{lod, ospf};

    fn accepted_pair() -> (ExampleRun<LodOutput>, ExampleRun<OspfOutput>) {
        let lod_input = lod::scenario("budget-cut").expect("built-in LOD scenario");
        let ospf_input = ospf::scenario("unique-shortest").expect("built-in OSPF scenario");
        let lod_run = lod::run_lod("budget-cut", &lod_input, lod::LodFault::None).expect("LOD");
        let ospf_run =
            ospf::run_ospf("unique-shortest", &ospf_input, ospf::OspfFault::None).expect("OSPF");
        assert!(lod_run.passed());
        assert!(ospf_run.passed());
        (lod_run, ospf_run)
    }

    #[test]
    fn registered_relation_passes() {
        let (lod, ospf) = accepted_pair();
        let report = compare(&lod, &ospf, &RelationSpec::registered());
        assert!(report.passed, "{:#?}", report.errors);
        assert_eq!(report.shared_nodes.len(), 4);
        assert_eq!(report.shared_edges.len(), 3);
    }

    #[test]
    fn misregistered_correspondence_fails_while_domains_stay_green() {
        let (lod, ospf) = accepted_pair();
        assert!(lod.passed());
        assert!(ospf.passed());
        let report = compare(&lod, &ospf, &RelationSpec::misregistered_control());
        assert!(!report.passed);
        assert!(report
            .errors
            .iter()
            .any(|error| error.contains("undeclared correspondence")));
    }
}
