use crate::{generated, AlgorithmCase, AlgorithmInput, AlgorithmOutput, CompositionResult};
use formal_example_structures::{
    run_memoization, MemoNode, MemoizationControl, MemoizationProblem, StructureError, TraceLog,
};

#[derive(Clone)]
pub(crate) enum State {
    Empty,
    Span { start: usize, end: usize },
}

fn state_id(start: usize, end: usize) -> String {
    format!("span-{start:04}-{end:04}")
}

pub(crate) fn build_problem(characters: &[char]) -> Result<Vec<MemoNode<State>>, StructureError> {
    if characters.is_empty() {
        return Ok(vec![MemoNode::new("empty", Vec::new(), State::Empty)?]);
    }
    let mut nodes = Vec::new();
    for length in 1..=characters.len() {
        for start in 0..=characters.len() - length {
            let end = start + length - 1;
            let dependencies = if length == 1 {
                Vec::new()
            } else if characters[start] == characters[end] {
                if length == 2 {
                    Vec::new()
                } else {
                    vec![state_id(start + 1, end - 1)]
                }
            } else {
                vec![state_id(start + 1, end), state_id(start, end - 1)]
            };
            nodes.push(MemoNode::new(
                state_id(start, end),
                dependencies,
                State::Span { start, end },
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
    let AlgorithmInput::Text { text } = input else {
        return Err(StructureError::new(
            "longest palindromic subsequence requires text",
        ));
    };
    let characters: Vec<char> = text.chars().collect();
    if characters.len() > 1000 {
        return Err(StructureError::new(
            "longest palindromic subsequence supports at most 1000 characters",
        ));
    }
    let result_id = if characters.is_empty() {
        "empty".to_string()
    } else {
        state_id(0, characters.len() - 1)
    };
    let mut trace = TraceLog::default();
    let result = run_memoization(
        MemoizationProblem::new(build_problem(&characters)?, result_id)?,
        |node, stored| match node.state() {
            State::Empty => Ok(vec![0_i64]),
            State::Span { start, end } if start == end => Ok(vec![1_i64]),
            State::Span { start, end } if characters[*start] == characters[*end] => {
                if end - start == 1 {
                    Ok(vec![2_i64])
                } else {
                    Ok(vec![
                        stored
                            .get(&state_id(start + 1, end - 1))
                            .copied()
                            .ok_or_else(|| StructureError::new("LPS inner span is absent"))?
                            + 2,
                    ])
                }
            }
            State::Span { .. } => node
                .dependencies()
                .iter()
                .map(|dependency| {
                    stored.get(dependency).copied().ok_or_else(|| {
                        StructureError::new(format!("LPS dependency {dependency} is absent"))
                    })
                })
                .collect(),
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
            AlgorithmInput::Text {
                text: "bbbab".to_string(),
            },
        ),
        AlgorithmCase::new(
            "pair",
            AlgorithmInput::Text {
                text: "cbbd".to_string(),
            },
        ),
        AlgorithmCase::new(
            "empty",
            AlgorithmInput::Text {
                text: String::new(),
            },
        ),
        AlgorithmCase::new(
            "single",
            AlgorithmInput::Text {
                text: "a".to_string(),
            },
        ),
    ];
    let mut generator = generated::Generator::new(69);
    for index in 0..1000 {
        cases.push(AlgorithmCase::new(
            generated::scenario(index),
            AlgorithmInput::Text {
                text: generator.text(9, 3),
            },
        ));
    }
    cases
}
