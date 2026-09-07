use crate::{generated, AlgorithmCase, AlgorithmInput, AlgorithmOutput, CompositionResult};
use formal_example_structures::{
    run_memoization, MemoNode, MemoizationControl, MemoizationProblem, StructureError, TraceLog,
};

const INFINITY: i64 = 1_i64 << 60;

fn state_id(left: usize, right: usize) -> String {
    format!("prefix-{left:04}-{right:04}")
}

pub(crate) fn build_problem(
    left: &[char],
    right: &[char],
) -> Result<Vec<MemoNode<(usize, usize)>>, StructureError> {
    let mut nodes = Vec::new();
    for left_count in 0..=left.len() {
        for right_count in 0..=right.len() {
            let dependencies = if left_count == 0 || right_count == 0 {
                Vec::new()
            } else if left[left_count - 1] == right[right_count - 1] {
                vec![state_id(left_count - 1, right_count - 1)]
            } else {
                vec![
                    state_id(left_count - 1, right_count),
                    state_id(left_count, right_count - 1),
                    state_id(left_count - 1, right_count - 1),
                ]
            };
            nodes.push(MemoNode::new(
                state_id(left_count, right_count),
                dependencies,
                (left_count, right_count),
            )?);
        }
    }
    Ok(nodes)
}

pub(crate) fn compose(
    input: &AlgorithmInput,
    scope: &str,
    control: MemoizationControl,
) -> Result<CompositionResult, StructureError> {
    let AlgorithmInput::TextPair { left, right } = input else {
        return Err(StructureError::new("edit distance requires two strings"));
    };
    let left: Vec<char> = left.chars().collect();
    let right: Vec<char> = right.chars().collect();
    if left.len() > 500 || right.len() > 500 {
        return Err(StructureError::new(
            "edit distance supports strings of at most 500 characters",
        ));
    }
    let mut trace = TraceLog::default();
    let result = run_memoization(
        MemoizationProblem::new(
            build_problem(&left, &right)?,
            state_id(left.len(), right.len()),
        )?,
        |node, stored| {
            let (left_count, right_count) = *node.state();
            if left_count == 0 {
                return Ok(vec![right_count as i64]);
            }
            if right_count == 0 {
                return Ok(vec![left_count as i64]);
            }
            if left[left_count - 1] == right[right_count - 1] {
                return Ok(vec![stored
                    .get(&state_id(left_count - 1, right_count - 1))
                    .copied()
                    .ok_or_else(|| {
                        StructureError::new("edit-distance diagonal is absent")
                    })?]);
            }
            node.dependencies()
                .iter()
                .map(|dependency| {
                    Ok(stored.get(dependency).copied().ok_or_else(|| {
                        StructureError::new(format!(
                            "edit-distance dependency {dependency} is absent"
                        ))
                    })? + 1)
                })
                .collect()
        },
        INFINITY,
        i64::min,
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
            AlgorithmInput::TextPair {
                left: "horse".to_string(),
                right: "ros".to_string(),
            },
        ),
        AlgorithmCase::new(
            "longer",
            AlgorithmInput::TextPair {
                left: "intention".to_string(),
                right: "execution".to_string(),
            },
        ),
        AlgorithmCase::new(
            "empty-left",
            AlgorithmInput::TextPair {
                left: String::new(),
                right: "abc".to_string(),
            },
        ),
        AlgorithmCase::new(
            "identical",
            AlgorithmInput::TextPair {
                left: "same".to_string(),
                right: "same".to_string(),
            },
        ),
    ];
    let mut generator = generated::Generator::new(67);
    for index in 0..1000 {
        cases.push(AlgorithmCase::new(
            generated::scenario(index),
            AlgorithmInput::TextPair {
                left: generator.text(7, 3),
                right: generator.text(7, 3),
            },
        ));
    }
    cases
}
