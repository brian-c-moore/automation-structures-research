use crate::{generated, AlgorithmCase, AlgorithmInput, AlgorithmOutput, CompositionResult};
use formal_example_structures::{
    run_memoization, MemoNode, MemoizationControl, MemoizationProblem, StructureError, TraceLog,
};

fn state_id(step: u32) -> String {
    format!("step-{step:04}")
}

pub(crate) fn build_problem(steps: u32) -> Result<Vec<MemoNode<u32>>, StructureError> {
    (0..=steps)
        .map(|step| {
            let dependencies = if step < 2 {
                Vec::new()
            } else {
                vec![state_id(step - 1), state_id(step - 2)]
            };
            MemoNode::new(state_id(step), dependencies, step)
        })
        .collect()
}

pub(crate) fn compose(
    input: &AlgorithmInput,
    scope: &str,
    control: MemoizationControl,
) -> Result<CompositionResult, StructureError> {
    let AlgorithmInput::Steps { steps } = input else {
        return Err(StructureError::new("climbing stairs requires a step count"));
    };
    if *steps > 45 {
        return Err(StructureError::new(
            "climbing stairs supports at most 45 steps",
        ));
    }
    let mut trace = TraceLog::default();
    let result = run_memoization(
        MemoizationProblem::new(build_problem(*steps)?, state_id(*steps))?,
        |node, values| {
            if *node.state() < 2 {
                Ok(vec![1_i64])
            } else {
                node.dependencies()
                    .iter()
                    .map(|dependency| {
                        values.get(dependency).copied().ok_or_else(|| {
                            StructureError::new(format!(
                                "climbing-stairs dependency {dependency} is absent"
                            ))
                        })
                    })
                    .collect()
            }
        },
        0_i64,
        |left, right| left + right,
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
        AlgorithmCase::new("baseline", AlgorithmInput::Steps { steps: 10 }),
        AlgorithmCase::new("zero-steps", AlgorithmInput::Steps { steps: 0 }),
        AlgorithmCase::new("one-step", AlgorithmInput::Steps { steps: 1 }),
        AlgorithmCase::new("two-steps", AlgorithmInput::Steps { steps: 2 }),
    ];
    let mut generator = generated::Generator::new(60);
    for index in 0..1000 {
        cases.push(AlgorithmCase::new(
            generated::scenario(index),
            AlgorithmInput::Steps {
                steps: generator.usize(36) as u32,
            },
        ));
    }
    cases
}
