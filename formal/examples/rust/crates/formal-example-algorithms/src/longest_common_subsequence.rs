use crate::{generated, AlgorithmCase, AlgorithmInput, AlgorithmOutput, CompositionResult};
use formal_example_structures::{
    run_memoization, MemoNode, MemoizationControl, MemoizationProblem, StructureError, TraceLog,
};

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
        return Err(StructureError::new(
            "longest common subsequence requires two strings",
        ));
    };
    let left: Vec<char> = left.chars().collect();
    let right: Vec<char> = right.chars().collect();
    if left.len() > 1000 || right.len() > 1000 {
        return Err(StructureError::new(
            "longest common subsequence supports strings of at most 1000 characters",
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
            if left_count == 0 || right_count == 0 {
                return Ok(vec![0_i64]);
            }
            if left[left_count - 1] == right[right_count - 1] {
                let diagonal = stored
                    .get(&state_id(left_count - 1, right_count - 1))
                    .copied()
                    .ok_or_else(|| StructureError::new("LCS diagonal state is absent"))?;
                Ok(vec![diagonal + 1])
            } else {
                node.dependencies()
                    .iter()
                    .map(|dependency| {
                        stored.get(dependency).copied().ok_or_else(|| {
                            StructureError::new(format!("LCS dependency {dependency} is absent"))
                        })
                    })
                    .collect()
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
            AlgorithmInput::TextPair {
                left: "abcde".to_string(),
                right: "ace".to_string(),
            },
        ),
        AlgorithmCase::new(
            "disjoint",
            AlgorithmInput::TextPair {
                left: "abc".to_string(),
                right: "def".to_string(),
            },
        ),
        AlgorithmCase::new(
            "identical",
            AlgorithmInput::TextPair {
                left: "abc".to_string(),
                right: "abc".to_string(),
            },
        ),
        AlgorithmCase::new(
            "empty-left",
            AlgorithmInput::TextPair {
                left: String::new(),
                right: "abc".to_string(),
            },
        ),
    ];
    let mut generator = generated::Generator::new(66);
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
