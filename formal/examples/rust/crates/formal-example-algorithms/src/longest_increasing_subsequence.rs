use crate::{generated, AlgorithmCase, AlgorithmInput, AlgorithmOutput, CompositionResult};
use formal_example_structures::{
    run_memoization, MemoNode, MemoizationControl, MemoizationProblem, StructureError, TraceLog,
};

#[derive(Clone)]
pub(crate) enum State {
    Element,
    Result,
}

fn element_id(index: usize) -> String {
    format!("element-{index:04}")
}

pub(crate) fn build_problem(values: &[i64]) -> Result<Vec<MemoNode<State>>, StructureError> {
    let mut nodes = Vec::new();
    for index in 0..values.len() {
        let dependencies = (0..index)
            .filter(|prior| values[*prior] < values[index])
            .map(element_id)
            .collect();
        nodes.push(MemoNode::new(
            element_id(index),
            dependencies,
            State::Element,
        )?);
    }
    nodes.push(MemoNode::new(
        "result",
        (0..values.len()).map(element_id).collect(),
        State::Result,
    )?);
    Ok(nodes)
}

pub(crate) fn compose(
    input: &AlgorithmInput,
    scope: &str,
    control: MemoizationControl,
) -> Result<CompositionResult, StructureError> {
    let AlgorithmInput::Numbers { values } = input else {
        return Err(StructureError::new(
            "longest increasing subsequence requires a number list",
        ));
    };
    if values.len() > 2500 {
        return Err(StructureError::new(
            "longest increasing subsequence supports at most 2500 values",
        ));
    }
    let mut trace = TraceLog::default();
    let result = run_memoization(
        MemoizationProblem::new(build_problem(values)?, "result")?,
        |node, stored| match node.state() {
            State::Element => {
                let mut candidates = vec![1_i64];
                for dependency in node.dependencies() {
                    candidates.push(
                        stored.get(dependency).copied().ok_or_else(|| {
                            StructureError::new(format!(
                                "increasing-subsequence dependency {dependency} is absent"
                            ))
                        })? + 1,
                    );
                }
                Ok(candidates)
            }
            State::Result => {
                let mut candidates = vec![0_i64];
                for dependency in node.dependencies() {
                    candidates.push(stored.get(dependency).copied().ok_or_else(|| {
                        StructureError::new(format!(
                            "increasing-subsequence result dependency {dependency} is absent"
                        ))
                    })?);
                }
                Ok(candidates)
            }
        },
        i64::MIN,
        i64::max,
        &mut trace,
        scope,
        control,
    )?;
    Ok(CompositionResult {
        output: AlgorithmOutput::Integer(result.result),
        trace,
        admitted_states: result.admitted_states,
        stored_states: result.stored_states,
        scope: scope.to_string(),
    })
}

pub(crate) fn cases() -> Vec<AlgorithmCase> {
    let mut cases = vec![
        AlgorithmCase::new(
            "baseline",
            AlgorithmInput::Numbers {
                values: vec![10, 9, 2, 5, 3, 7, 101, 18],
            },
        ),
        AlgorithmCase::new("empty", AlgorithmInput::Numbers { values: vec![] }),
        AlgorithmCase::new(
            "duplicates",
            AlgorithmInput::Numbers {
                values: vec![7, 7, 7],
            },
        ),
        AlgorithmCase::new(
            "mixed",
            AlgorithmInput::Numbers {
                values: vec![0, 1, 0, 3, 2, 3],
            },
        ),
    ];
    let mut generator = generated::Generator::new(62);
    for index in 0..1000 {
        cases.push(AlgorithmCase::new(
            generated::scenario(index),
            AlgorithmInput::Numbers {
                values: generator.numbers(12, -10, 20),
            },
        ));
    }
    cases
}
