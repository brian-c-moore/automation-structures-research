use crate::{generated, AlgorithmCase, AlgorithmInput, AlgorithmOutput, CompositionResult};
use formal_example_structures::{
    run_memoization, MemoNode, MemoizationControl, MemoizationProblem, StructureError, TraceLog,
};

fn state_id(count: usize) -> String {
    format!("prefix-{count:04}")
}

pub(crate) fn build_problem(values: &[i64]) -> Result<Vec<MemoNode<usize>>, StructureError> {
    (0..=values.len())
        .map(|count| {
            let dependencies = match count {
                0 => Vec::new(),
                1 => vec![state_id(0)],
                _ => vec![state_id(count - 1), state_id(count - 2)],
            };
            MemoNode::new(state_id(count), dependencies, count)
        })
        .collect()
}

pub(crate) fn compose(
    input: &AlgorithmInput,
    scope: &str,
    control: MemoizationControl,
) -> Result<CompositionResult, StructureError> {
    let AlgorithmInput::Numbers { values } = input else {
        return Err(StructureError::new("house robber requires a number list"));
    };
    if values.len() > 100 || values.iter().any(|value| !(0..=400).contains(value)) {
        return Err(StructureError::new(
            "house robber requires at most 100 values from 0 through 400",
        ));
    }
    let mut trace = TraceLog::default();
    let result = run_memoization(
        MemoizationProblem::new(build_problem(values)?, state_id(values.len()))?,
        |node, stored| {
            let count = *node.state();
            if count == 0 {
                return Ok(vec![0_i64]);
            }
            let skip = stored
                .get(&state_id(count - 1))
                .copied()
                .ok_or_else(|| StructureError::new("house-robber skip state is absent"))?;
            let earlier = if count >= 2 {
                stored
                    .get(&state_id(count - 2))
                    .copied()
                    .ok_or_else(|| StructureError::new("house-robber take state is absent"))?
            } else {
                0
            };
            Ok(vec![skip, earlier + values[count - 1]])
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
                values: vec![2, 7, 9, 3, 1],
            },
        ),
        AlgorithmCase::new("empty", AlgorithmInput::Numbers { values: vec![] }),
        AlgorithmCase::new("single-house", AlgorithmInput::Numbers { values: vec![5] }),
        AlgorithmCase::new(
            "separated-pair",
            AlgorithmInput::Numbers {
                values: vec![2, 1, 1, 2],
            },
        ),
    ];
    let mut generator = generated::Generator::new(61);
    for index in 0..1000 {
        cases.push(AlgorithmCase::new(
            generated::scenario(index),
            AlgorithmInput::Numbers {
                values: generator.numbers(12, 0, 30),
            },
        ));
    }
    cases
}
