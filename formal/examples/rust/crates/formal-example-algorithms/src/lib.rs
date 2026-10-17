mod climbing_stairs;
mod coin_change;
mod edit_distance;
pub mod evidence;
mod generated;
mod house_robber;
mod knapsack_01;
mod longest_common_subsequence;
mod longest_increasing_subsequence;
mod longest_palindromic_subsequence;
pub mod references;
pub mod schema;
mod unique_paths;
mod word_break;

use formal_example_structures::{
    memoization_subject, MemoizationControl, StructureError, TraceLog, MEMOIZATION_EDGES,
    MEMOIZATION_STRUCTURES,
};
use serde::Serialize;

pub const ALGORITHM_IDS: [&str; 10] = [
    "FEX-ALG-060",
    "FEX-ALG-061",
    "FEX-ALG-062",
    "FEX-ALG-063",
    "FEX-ALG-064",
    "FEX-ALG-065",
    "FEX-ALG-066",
    "FEX-ALG-067",
    "FEX-ALG-068",
    "FEX-ALG-069",
];

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum AlgorithmInput {
    Steps {
        steps: u32,
    },
    Numbers {
        values: Vec<i64>,
    },
    CoinChange {
        coins: Vec<u32>,
        amount: u32,
    },
    WordBreak {
        text: String,
        dictionary: Vec<String>,
    },
    Grid {
        rows: u32,
        columns: u32,
    },
    TextPair {
        left: String,
        right: String,
    },
    Knapsack {
        weights: Vec<u32>,
        values: Vec<i64>,
        capacity: u32,
    },
    Text {
        text: String,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", content = "value", rename_all = "kebab-case")]
pub enum AlgorithmOutput {
    Integer(i64),
    Boolean(bool),
}

impl AlgorithmOutput {
    fn corrupt(&self) -> Self {
        match self {
            Self::Integer(value) => Self::Integer(value.saturating_add(1)),
            Self::Boolean(value) => Self::Boolean(!value),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct AlgorithmCheck {
    pub name: String,
    pub passed: bool,
    pub detail: String,
}

impl AlgorithmCheck {
    pub fn verdict(name: impl Into<String>, passed: bool, detail: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            passed,
            detail: detail.into(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct AlgorithmCase {
    pub scenario: String,
    pub input: AlgorithmInput,
}

impl AlgorithmCase {
    pub fn new(scenario: impl Into<String>, input: AlgorithmInput) -> Self {
        Self {
            scenario: scenario.into(),
            input,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AlgorithmFault {
    None,
    CorruptOutput,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CompositionResult {
    pub output: AlgorithmOutput,
    pub trace: TraceLog,
    pub admitted_states: usize,
    pub stored_states: usize,
    pub scope: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct AlgorithmRun {
    pub id: String,
    pub name: String,
    pub scenario: String,
    pub input: AlgorithmInput,
    pub output: AlgorithmOutput,
    pub reference: AlgorithmOutput,
    pub checks: Vec<AlgorithmCheck>,
    pub trace: TraceLog,
    pub admitted_states: usize,
    pub stored_states: usize,
    pub residuals: Vec<String>,
}

impl AlgorithmRun {
    pub fn passed(&self) -> bool {
        !self.checks.is_empty()
            && !self.trace.events().is_empty()
            && self.checks.iter().all(|check| check.passed)
            && evidence::describe(&self.id).is_ok_and(|record| {
                self.trace.events().iter().all(|event| {
                    let actual = event.structure.implementation_identity(Some(&event.action));
                    actual.is_some()
                        && actual == event.implementation_identity
                        && record.record.construction.nodes.iter().any(|node| {
                            node.stratum == formal_example_structures::ConstructionStratum::Catalog
                                && node.id == event.structure.name()
                                && actual == Some(node.implementation_identity.as_str())
                        })
                })
            })
    }
}

pub fn name(id: &str) -> Option<&'static str> {
    match id {
        "FEX-ALG-060" => Some("Climbing Stairs"),
        "FEX-ALG-061" => Some("House Robber"),
        "FEX-ALG-062" => Some("Longest Increasing Subsequence"),
        "FEX-ALG-063" => Some("Coin Change"),
        "FEX-ALG-064" => Some("Word Break"),
        "FEX-ALG-065" => Some("Unique Paths"),
        "FEX-ALG-066" => Some("Longest Common Subsequence"),
        "FEX-ALG-067" => Some("Edit Distance"),
        "FEX-ALG-068" => Some("0/1 Knapsack"),
        "FEX-ALG-069" => Some("Longest Palindromic Subsequence"),
        _ => None,
    }
}

pub fn cases(id: &str) -> Result<Vec<AlgorithmCase>, String> {
    match id {
        "FEX-ALG-060" => Ok(climbing_stairs::cases()),
        "FEX-ALG-061" => Ok(house_robber::cases()),
        "FEX-ALG-062" => Ok(longest_increasing_subsequence::cases()),
        "FEX-ALG-063" => Ok(coin_change::cases()),
        "FEX-ALG-064" => Ok(word_break::cases()),
        "FEX-ALG-065" => Ok(unique_paths::cases()),
        "FEX-ALG-066" => Ok(longest_common_subsequence::cases()),
        "FEX-ALG-067" => Ok(edit_distance::cases()),
        "FEX-ALG-068" => Ok(knapsack_01::cases()),
        "FEX-ALG-069" => Ok(longest_palindromic_subsequence::cases()),
        _ => Err(format!("unknown Memoization algorithm {id}")),
    }
}

fn compose(
    id: &str,
    input: &AlgorithmInput,
    scope: &str,
    control: MemoizationControl,
) -> Result<CompositionResult, StructureError> {
    match id {
        "FEX-ALG-060" => climbing_stairs::compose(input, scope, control),
        "FEX-ALG-061" => house_robber::compose(input, scope, control),
        "FEX-ALG-062" => longest_increasing_subsequence::compose(input, scope, control),
        "FEX-ALG-063" => coin_change::compose(input, scope, control),
        "FEX-ALG-064" => word_break::compose(input, scope, control),
        "FEX-ALG-065" => unique_paths::compose(input, scope, control),
        "FEX-ALG-066" => longest_common_subsequence::compose(input, scope, control),
        "FEX-ALG-067" => edit_distance::compose(input, scope, control),
        "FEX-ALG-068" => knapsack_01::compose(input, scope, control),
        "FEX-ALG-069" => longest_palindromic_subsequence::compose(input, scope, control),
        _ => Err(StructureError::new(format!(
            "unknown Memoization algorithm {id}"
        ))),
    }
}

pub fn run(
    id: &str,
    scenario: Option<&str>,
    control: MemoizationControl,
    fault: AlgorithmFault,
) -> Result<AlgorithmRun, String> {
    let algorithm_name = name(id).ok_or_else(|| format!("unknown Memoization algorithm {id}"))?;
    let available = cases(id)?;
    let selected = match scenario {
        Some(scenario) => available
            .into_iter()
            .find(|case| case.scenario == scenario)
            .ok_or_else(|| format!("unknown {id} scenario {scenario}"))?,
        None => available
            .into_iter()
            .next()
            .ok_or_else(|| format!("{id} has no cases"))?,
    };
    let scope = format!("{id}::{}", selected.scenario);
    let composition =
        compose(id, &selected.input, &scope, control).map_err(|error| error.to_string())?;
    let reference = references::evaluate(id, &selected.input)?;
    let output = if fault == AlgorithmFault::CorruptOutput {
        composition.output.corrupt()
    } else {
        composition.output.clone()
    };
    let subject = memoization_subject(&composition.scope);
    let recipe =
        composition
            .trace
            .verify_recipe_for(&subject, &MEMOIZATION_STRUCTURES, &MEMOIZATION_EDGES);
    Ok(AlgorithmRun {
        id: id.to_string(),
        name: algorithm_name.to_string(),
        scenario: selected.scenario,
        input: selected.input,
        checks: vec![
            AlgorithmCheck::verdict(
                "output-matches-independent-reference",
                output == reference,
                "The Memoization construction and the separately written reference agree exactly.",
            ),
            AlgorithmCheck::verdict(
                "memoization-recipe",
                recipe.is_ok(),
                recipe
                    .err()
                    .map(|error| error.to_string())
                    .unwrap_or_else(|| {
                        "All registered memoization structures and edges occurred.".to_string()
                    }),
            ),
            AlgorithmCheck::verdict(
                "state-accounting",
                composition.admitted_states == composition.stored_states,
                format!(
                    "admitted={} stored={}",
                    composition.admitted_states, composition.stored_states
                ),
            ),
        ],
        output,
        reference,
        trace: composition.trace,
        admitted_states: composition.admitted_states,
        stored_states: composition.stored_states,
        residuals: vec![
            "The result is bounded to the registered finite input contract.".to_string(),
            "Runtime and memory-complexity claims are excluded.".to_string(),
        ],
    })
}

#[cfg(test)]
#[test]
fn memoization_rejects_another_reduction_operation_with_unchanged_checks() {
    let mut run = run(
        "FEX-ALG-060",
        None,
        MemoizationControl::None,
        AlgorithmFault::None,
    )
    .expect("actual Memoization fold");
    assert!(run.passed());
    let trace = std::mem::take(&mut run.trace);
    assert!(!run.passed(), "erased Memoization trace");
    run.trace = trace;
    let checks = std::mem::take(&mut run.checks);
    assert!(!run.passed(), "erased Memoization checks");
    run.checks = checks;
    let mut comparison = TraceLog::default();
    formal_example_structures::PathReduction::compare(None, 1, &mut comparison, "memoization");
    run.trace = comparison;
    assert!(
        !run.passed(),
        "unchanged result/checks cannot relabel a comparison as a fold"
    );
}

#[cfg(test)]
fn assert_algorithm(id: &str) {
    for case in cases(id).expect("registered algorithm cases") {
        let run = run(
            id,
            Some(&case.scenario),
            MemoizationControl::None,
            AlgorithmFault::None,
        )
        .expect("algorithm run");
        assert!(run.passed(), "{id} {} failed", case.scenario);
    }
}

#[cfg(test)]
mod algorithm_claims {
    use super::*;

    macro_rules! claim_test {
        ($test:ident, $id:literal) => {
            #[test]
            fn $test() {
                assert_algorithm($id);
            }
        };
    }

    claim_test!(fex_alg_060, "FEX-ALG-060");
    claim_test!(fex_alg_061, "FEX-ALG-061");
    claim_test!(fex_alg_062, "FEX-ALG-062");
    claim_test!(fex_alg_063, "FEX-ALG-063");
    claim_test!(fex_alg_064, "FEX-ALG-064");
    claim_test!(fex_alg_065, "FEX-ALG-065");
    claim_test!(fex_alg_066, "FEX-ALG-066");
    claim_test!(fex_alg_067, "FEX-ALG-067");
    claim_test!(fex_alg_068, "FEX-ALG-068");
    claim_test!(fex_alg_069, "FEX-ALG-069");

    #[test]
    fn generated_case_inventory_has_declared_distinct_counts() {
        let expected = [
            ("FEX-ALG-060", 36),
            ("FEX-ALG-061", 881),
            ("FEX-ALG-062", 873),
            ("FEX-ALG-063", 82),
            ("FEX-ALG-064", 518),
            ("FEX-ALG-065", 4),
            ("FEX-ALG-066", 1_000),
            ("FEX-ALG-067", 1_000),
            ("FEX-ALG-068", 833),
            ("FEX-ALG-069", 545),
        ];
        for (id, expected_distinct) in expected {
            let generated = cases(id)
                .expect("cases")
                .into_iter()
                .filter(|case| case.scenario.starts_with("generated-"))
                .collect::<Vec<_>>();
            let distinct = generated
                .iter()
                .map(|case| &case.input)
                .collect::<std::collections::HashSet<_>>()
                .len();
            assert_eq!(generated.len(), 1_000, "{id}");
            assert_eq!(distinct, expected_distinct, "{id}");
        }
    }

    #[test]
    fn inherited_controls_break_binding_without_changing_default_results() {
        for id in ALGORITHM_IDS {
            let case = cases(id).expect("cases").remove(0);
            for control in [
                MemoizationControl::BypassRegistry,
                MemoizationControl::BypassTraversal,
                MemoizationControl::BypassReduction,
            ] {
                let run = run(id, Some(&case.scenario), control, AlgorithmFault::None)
                    .expect("controlled run");
                assert_eq!(run.output, run.reference, "{id} {control:?}");
                assert!(run
                    .checks
                    .iter()
                    .any(|check| check.name == "memoization-recipe" && !check.passed));
            }
        }
    }

    #[test]
    fn each_algorithm_oracle_control_is_discriminating() {
        for id in ALGORITHM_IDS {
            let case = cases(id).expect("cases").remove(0);
            let run = run(
                id,
                Some(&case.scenario),
                MemoizationControl::None,
                AlgorithmFault::CorruptOutput,
            )
            .expect("faulted run");
            assert!(
                run.checks
                    .iter()
                    .any(|check| check.name == "output-matches-independent-reference"
                        && !check.passed)
            );
            assert!(run
                .checks
                .iter()
                .any(|check| check.name == "memoization-recipe" && check.passed));
        }
    }

    #[test]
    fn numeric_output_and_allocation_bounds_are_enforced() {
        assert!(house_robber::compose(
            &AlgorithmInput::Numbers { values: vec![401] },
            "invalid-house-value",
            MemoizationControl::None,
        )
        .is_err());
        assert!(unique_paths::compose(
            &AlgorithmInput::Grid {
                rows: 34,
                columns: 35,
            },
            "invalid-grid-sum",
            MemoizationControl::None,
        )
        .is_err());
        assert!(knapsack_01::compose(
            &AlgorithmInput::Knapsack {
                weights: vec![1],
                values: vec![1],
                capacity: 201,
            },
            "invalid-knapsack-capacity",
            MemoizationControl::None,
        )
        .is_err());
        assert!(knapsack_01::compose(
            &AlgorithmInput::Knapsack {
                weights: vec![1, 1],
                values: vec![i64::MAX, 1],
                capacity: 2,
            },
            "invalid-knapsack-value-sum",
            MemoizationControl::None,
        )
        .is_err());
    }
}
