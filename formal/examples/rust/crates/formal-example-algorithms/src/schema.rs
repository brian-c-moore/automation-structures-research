use crate::{AlgorithmCheck, AlgorithmOutput};
use formal_example_structures::{
    memoization_subject, run_memoization, MemoNode, MemoizationControl, MemoizationProblem,
    StructureError, TraceLog, MEMOIZATION_EDGES, MEMOIZATION_STRUCTURES,
};
use serde::Serialize;

pub const ID: &str = "FEX-SC-C01";

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct SchemaRun {
    pub id: String,
    pub scenario: String,
    pub output: AlgorithmOutput,
    pub reference: AlgorithmOutput,
    pub checks: Vec<AlgorithmCheck>,
    pub trace: TraceLog,
    pub admitted_states: usize,
    pub stored_states: usize,
    pub residuals: Vec<String>,
}

impl SchemaRun {
    pub fn passed(&self) -> bool {
        self.checks.iter().all(|check| check.passed)
    }
}

pub fn run(control: MemoizationControl) -> Result<SchemaRun, StructureError> {
    let scope = "memoization-schema::diamond";
    let nodes = vec![
        MemoNode::new("left", Vec::new(), 2_i64)?,
        MemoNode::new("right", Vec::new(), 3_i64)?,
        MemoNode::new(
            "result",
            vec!["left".to_string(), "right".to_string()],
            0_i64,
        )?,
    ];
    let mut trace = TraceLog::default();
    let result = run_memoization(
        MemoizationProblem::new(nodes, "result")?,
        |node, values| {
            if node.dependencies().is_empty() {
                Ok(vec![*node.state()])
            } else {
                Ok(node
                    .dependencies()
                    .iter()
                    .map(|dependency| {
                        values.get(dependency).copied().ok_or_else(|| {
                            StructureError::new(format!("schema dependency {dependency} is absent"))
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?)
            }
        },
        0_i64,
        |left, right| left + right,
        &mut trace,
        scope,
        control,
    )?;
    let reference = crate::references::memoization_fixture();
    let subject = memoization_subject(scope);
    let recipe = trace.verify_recipe_for(&subject, &MEMOIZATION_STRUCTURES, &MEMOIZATION_EDGES);
    let output = AlgorithmOutput::Integer(result.result);
    Ok(SchemaRun {
        id: ID.to_string(),
        scenario: "diamond".to_string(),
        checks: vec![
            AlgorithmCheck::verdict(
                "schema-reference-agreement",
                output == reference,
                "The dependency diamond equals the separate direct sum reference.",
            ),
            AlgorithmCheck::verdict(
                "memoization-recipe",
                recipe.is_ok(),
                recipe
                    .err()
                    .map(|error| error.to_string())
                    .unwrap_or_else(|| "All registered memoization structures and edges occurred.".to_string()),
            ),
            AlgorithmCheck::verdict(
                "state-accounting",
                result.admitted_states == result.stored_states,
                format!(
                    "admitted={} stored={}",
                    result.admitted_states, result.stored_states
                ),
            ),
        ],
        output,
        reference,
        trace,
        admitted_states: result.admitted_states,
        stored_states: result.stored_states,
        residuals: vec![
            "This fixture checks the reusable composition, not every dynamic-programming recurrence."
                .to_string(),
            "Algorithm instances bind their own input contracts and independent references."
                .to_string(),
        ],
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn schema_claim() {
        let baseline = run(MemoizationControl::None).expect("schema fixture");
        assert!(baseline.passed());
        for control in [
            MemoizationControl::BypassRegistry,
            MemoizationControl::BypassTraversal,
            MemoizationControl::BypassReduction,
        ] {
            let controlled = run(control).expect("controlled schema fixture");
            assert_eq!(controlled.output, controlled.reference);
            assert!(controlled
                .checks
                .iter()
                .any(|check| check.name == "memoization-recipe" && !check.passed));
        }
    }
}
