use crate::{references, Check, ExampleRun};
use formal_example_structures::{
    rooted_frontier_subject, run_bounded_frontier, AllocationRecord, BoundedFrontierControl, Bytes,
    FrontierCandidate, FrontierTarget, QualityNode, StructureError, TraceLog,
    BOUNDED_FRONTIER_EDGES, BOUNDED_FRONTIER_STRUCTURES,
};
use serde::Serialize;
use std::cmp::Reverse;
use std::collections::BTreeSet;

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct LodLevel {
    pub id: String,
    pub hierarchy_level: u32,
    pub bytes: u64,
    pub utility: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct LodObject {
    pub id: String,
    pub view_weight: u64,
    pub levels: Vec<LodLevel>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct LodInput {
    pub byte_budget: u64,
    pub objects: Vec<LodObject>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct LodChoice {
    pub object_id: String,
    pub level_id: String,
    pub bytes: u64,
    pub weighted_utility: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct LodOutput {
    pub selected: Vec<LodChoice>,
    pub total_bytes: u64,
    pub total_utility: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LodFault {
    None,
    BypassDiscovery,
    BypassSelection,
    SkipBudgetCharge,
    OmitSnapshotTrace,
}

fn validate_input(input: &LodInput) -> Result<(), StructureError> {
    if input.objects.is_empty() {
        return Err(StructureError::new("LOD input has no objects"));
    }
    let mut object_ids = BTreeSet::new();
    let mut level_ids = BTreeSet::new();
    for object in &input.objects {
        if object.id.is_empty() || !object_ids.insert(&object.id) {
            return Err(StructureError::new(
                "LOD object IDs must be nonempty and unique",
            ));
        }
        if object.view_weight == 0 {
            return Err(StructureError::new(format!(
                "LOD object {} has zero view weight",
                object.id
            )));
        }
        if object.levels.is_empty() {
            return Err(StructureError::new(format!(
                "LOD object {} has no quality level",
                object.id
            )));
        }
        for level in &object.levels {
            let scoped_id = format!("{}::{}", object.id, level.id);
            if level.id.is_empty() || !level_ids.insert(scoped_id) {
                return Err(StructureError::new(format!(
                    "LOD object {} has an empty or duplicate level ID",
                    object.id
                )));
            }
        }
    }
    Ok(())
}

fn hierarchy_nodes(input: &LodInput) -> Vec<QualityNode> {
    let mut nodes = Vec::new();
    for object in &input.objects {
        let mut levels = object.levels.clone();
        levels.sort_by(|left, right| {
            right
                .hierarchy_level
                .cmp(&left.hierarchy_level)
                .then_with(|| left.id.cmp(&right.id))
        });
        for (index, level) in levels.iter().enumerate() {
            nodes.push(QualityNode {
                id: format!("{}::{}", object.id, level.id),
                parent: index
                    .checked_sub(1)
                    .map(|parent| format!("{}::{}", object.id, levels[parent].id)),
                level: level.hierarchy_level,
                cost: level.bytes,
            });
        }
    }
    nodes
}

fn frontier_targets(input: &LodInput) -> Result<Vec<FrontierTarget<LodChoice>>, StructureError> {
    input
        .objects
        .iter()
        .map(|object| {
            let options = object
                .levels
                .iter()
                .map(|level| {
                    let weighted_utility = level
                        .utility
                        .checked_mul(object.view_weight)
                        .ok_or_else(|| StructureError::new("LOD weighted utility overflow"))?;
                    let choice = LodChoice {
                        object_id: object.id.clone(),
                        level_id: level.id.clone(),
                        bytes: level.bytes,
                        weighted_utility,
                    };
                    Ok(FrontierCandidate {
                        node_id: format!("{}::{}", object.id, level.id),
                        record: AllocationRecord {
                            id: object.id.clone(),
                            cost: level.bytes,
                            value: choice,
                        },
                    })
                })
                .collect::<Result<Vec<_>, StructureError>>()?;
            Ok(FrontierTarget {
                id: object.id.clone(),
                candidates: options,
            })
        })
        .collect()
}

fn plan_rank(records: &[AllocationRecord<LodChoice>]) -> (Reverse<u128>, u64, Vec<LodChoice>) {
    let utility = records
        .iter()
        .map(|record| u128::from(record.value.weighted_utility))
        .sum();
    let bytes = records.iter().map(|record| record.cost).sum();
    let mut choices: Vec<_> = records.iter().map(|record| record.value.clone()).collect();
    choices.sort();
    (Reverse(utility), bytes, choices)
}

fn output_from_choices(mut choices: Vec<LodChoice>) -> Result<LodOutput, StructureError> {
    choices.sort();
    let total_bytes = choices.iter().try_fold(0u64, |sum, choice| {
        sum.checked_add(choice.bytes)
            .ok_or_else(|| StructureError::new("LOD byte total overflow"))
    })?;
    let total_utility = choices.iter().try_fold(0u64, |sum, choice| {
        sum.checked_add(choice.weighted_utility)
            .ok_or_else(|| StructureError::new("LOD utility total overflow"))
    })?;
    Ok(LodOutput {
        selected: choices,
        total_bytes,
        total_utility,
    })
}

pub fn run_lod(
    scenario: &str,
    input: &LodInput,
    fault: LodFault,
) -> Result<ExampleRun<LodOutput>, StructureError> {
    validate_input(input)?;
    let mut trace = TraceLog::default();
    let nodes = hierarchy_nodes(input);
    let targets = frontier_targets(input)?;
    let control = match fault {
        LodFault::None => BoundedFrontierControl::None,
        LodFault::BypassDiscovery => BoundedFrontierControl::BypassDiscovery,
        LodFault::BypassSelection => BoundedFrontierControl::BypassSelection,
        LodFault::SkipBudgetCharge => BoundedFrontierControl::SkipBudgetCharge,
        LodFault::OmitSnapshotTrace => BoundedFrontierControl::OmitSnapshotTrace,
    };
    let frontier = run_bounded_frontier::<Bytes, _, _>(
        nodes,
        targets,
        input.byte_budget,
        plan_rank,
        &mut trace,
        scenario,
        control,
    )?;
    let output = output_from_choices(
        frontier
            .snapshot
            .records()
            .iter()
            .map(|record| record.value.clone())
            .collect(),
    )?;
    let reference = references::lod_reference(input).map_err(StructureError::new)?;
    let frontier_subject = rooted_frontier_subject(scenario);
    let recipe = trace.verify_recipe_for(
        &frontier_subject,
        &BOUNDED_FRONTIER_STRUCTURES,
        &BOUNDED_FRONTIER_EDGES,
    );
    let checks = vec![
        Check::verdict(
            "independent-result",
            output == reference,
            "structure construction equals the separate exhaustive selector",
        ),
        Check::verdict(
            "budget-consistency",
            output.total_bytes <= input.byte_budget,
            format!(
                "selected={} capacity={}",
                output.total_bytes, input.byte_budget
            ),
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
            "hierarchy-obligations",
            format!("validated {} quality nodes", frontier.hierarchy_nodes),
        ),
        Check::pass(
            "rooted-frontier-selection",
            format!(
                "ranked {} candidates across {} complete plans",
                frontier.candidate_count, frontier.complete_plans
            ),
        ),
    ];
    Ok(ExampleRun {
        id: "FEX-DOM-REN-03".to_string(),
        scenario: scenario.to_string(),
        output,
        reference,
        checks,
        trace,
        residuals: vec![
            "No renderer, visibility system, streaming system, or GPU integration is claimed."
                .to_string(),
            "View scoring and fidelity utility are domain functions.".to_string(),
            "Temporal hysteresis and performance claims are excluded.".to_string(),
        ],
    })
}

pub fn scenarios() -> Vec<(&'static str, LodInput)> {
    let base = vec![
        LodObject {
            id: "terrain".to_string(),
            view_weight: 2,
            levels: vec![
                LodLevel {
                    id: "coarse".to_string(),
                    hierarchy_level: 3,
                    bytes: 3,
                    utility: 2,
                },
                LodLevel {
                    id: "medium".to_string(),
                    hierarchy_level: 2,
                    bytes: 6,
                    utility: 7,
                },
                LodLevel {
                    id: "fine".to_string(),
                    hierarchy_level: 1,
                    bytes: 12,
                    utility: 12,
                },
            ],
        },
        LodObject {
            id: "tree".to_string(),
            view_weight: 3,
            levels: vec![
                LodLevel {
                    id: "coarse".to_string(),
                    hierarchy_level: 3,
                    bytes: 2,
                    utility: 2,
                },
                LodLevel {
                    id: "medium".to_string(),
                    hierarchy_level: 2,
                    bytes: 5,
                    utility: 6,
                },
                LodLevel {
                    id: "fine".to_string(),
                    hierarchy_level: 1,
                    bytes: 9,
                    utility: 10,
                },
            ],
        },
    ];
    let mut changed_view = base.clone();
    changed_view[0].view_weight = 6;
    changed_view[1].view_weight = 1;
    vec![
        (
            "full-budget",
            LodInput {
                byte_budget: 32,
                objects: base.clone(),
            },
        ),
        (
            "budget-cut",
            LodInput {
                byte_budget: 11,
                objects: base.clone(),
            },
        ),
        (
            "zero-budget",
            LodInput {
                byte_budget: 0,
                objects: base,
            },
        ),
        (
            "view-change",
            LodInput {
                byte_budget: 11,
                objects: changed_view,
            },
        ),
    ]
}

pub fn scenario(name: &str) -> Option<LodInput> {
    scenarios()
        .into_iter()
        .find(|(scenario, _)| *scenario == name)
        .map(|(_, input)| input)
}

#[cfg(test)]
pub(crate) fn generated_input(seed: u64) -> LodInput {
    let mut state = seed.wrapping_add(0x9e3779b97f4a7c15);
    let mut next = || {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        state
    };
    let count = (next() % 3 + 1) as usize;
    let mut objects = Vec::new();
    for index in 0..count {
        let coarse = next() % 4 + 1;
        let fine = coarse + next() % 5 + 1;
        objects.push(LodObject {
            id: format!("object-{index}"),
            view_weight: next() % 5 + 1,
            levels: vec![
                LodLevel {
                    id: "coarse".to_string(),
                    hierarchy_level: 2,
                    bytes: coarse,
                    utility: next() % 5 + 1,
                },
                LodLevel {
                    id: "fine".to_string(),
                    hierarchy_level: 1,
                    bytes: fine,
                    utility: next() % 8 + 6,
                },
            ],
        });
    }
    LodInput {
        byte_budget: next() % 20,
        objects,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn domain_claim() {
        for (name, input) in scenarios() {
            let run = run_lod(name, &input, LodFault::None).expect("valid LOD fixture");
            assert!(run.passed(), "{name}: {:#?}", run.checks);
        }
        for seed in 0..64 {
            let input = generated_input(seed);
            let run = run_lod(&format!("generated-{seed}"), &input, LodFault::None)
                .expect("valid generated LOD input");
            assert!(run.passed(), "seed {seed}: {:#?}", run.checks);
        }
    }

    #[test]
    fn assembly_claim() {
        let scenarios = scenarios();
        let runs: Vec<_> = scenarios
            .iter()
            .map(|(name, input)| run_lod(name, input, LodFault::None).expect("valid fixture"))
            .collect();
        let reference = references::lod_assembly_reference(&scenarios).expect("assembly reference");
        let mut observed: Vec<_> = runs
            .iter()
            .map(|run| (run.scenario.clone(), run.output.clone()))
            .collect();
        observed.sort_by(|left, right| left.0.cmp(&right.0));
        assert_eq!(runs.len(), 4);
        assert_eq!(observed, reference);
        assert!(runs.iter().all(ExampleRun::passed));
        assert!(runs.iter().all(|run| !run.trace.events().is_empty()));
        assert_ne!(
            runs[1].output, runs[3].output,
            "view change must be observable"
        );
    }

    #[test]
    fn controls_are_discriminating() {
        let input = scenario("budget-cut").expect("built-in scenario");
        let undiscovered = run_lod("budget-cut", &input, LodFault::BypassDiscovery)
            .expect("discovery bypass still computes a domain result");
        assert_eq!(undiscovered.output, undiscovered.reference);
        assert!(!undiscovered.passed());
        assert!(undiscovered
            .checks
            .iter()
            .any(|check| check.name == "recipe-binding" && !check.passed));

        let unselected = run_lod("budget-cut", &input, LodFault::BypassSelection)
            .expect("selection bypass still commits a feasible result");
        assert!(!unselected.passed());
        assert!(unselected
            .checks
            .iter()
            .any(|check| check.name == "recipe-binding" && !check.passed));

        let detached = run_lod("budget-cut", &input, LodFault::OmitSnapshotTrace)
            .expect("detached snapshot still computes a domain result");
        assert_eq!(detached.output, detached.reference);
        assert!(!detached.passed());
        assert!(detached
            .checks
            .iter()
            .any(|check| check.name == "recipe-binding" && !check.passed));

        let bypass = run_lod("budget-cut", &input, LodFault::SkipBudgetCharge);
        assert!(
            bypass.is_err(),
            "uncharged allocation must violate snapshot capacity"
        );

        let baseline = run_lod("budget-cut", &input, LodFault::None).expect("baseline");
        assert!(baseline.passed());
    }
}
