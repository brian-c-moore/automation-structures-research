use crate::{generated, AlgorithmCase, AlgorithmInput, AlgorithmOutput, CompositionResult};
use formal_example_structures::{
    run_memoization, MemoNode, MemoizationControl, MemoizationProblem, StructureError, TraceLog,
};

fn state_id(items: usize, capacity: u32) -> String {
    format!("state-{items:03}-{capacity:05}")
}

pub(crate) fn build_problem(
    weights: &[u32],
    capacity: u32,
) -> Result<Vec<MemoNode<(usize, u32)>>, StructureError> {
    let mut nodes = Vec::new();
    for items in 0..=weights.len() {
        for current_capacity in 0..=capacity {
            let mut dependencies = Vec::new();
            if items > 0 {
                dependencies.push(state_id(items - 1, current_capacity));
                let weight = weights[items - 1];
                if weight <= current_capacity {
                    dependencies.push(state_id(items - 1, current_capacity - weight));
                }
            }
            nodes.push(MemoNode::new(
                state_id(items, current_capacity),
                dependencies,
                (items, current_capacity),
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
    let AlgorithmInput::Knapsack {
        weights,
        values,
        capacity,
    } = input
    else {
        return Err(StructureError::new(
            "0/1 knapsack requires weights, values, and capacity",
        ));
    };
    if weights.len() != values.len()
        || weights.len() > 20
        || weights.contains(&0)
        || weights.iter().any(|weight| *weight > 200)
        || values.iter().any(|value| *value < 0)
        || *capacity > 200
        || values
            .iter()
            .try_fold(0_i64, |total, value| total.checked_add(*value))
            .is_none()
    {
        return Err(StructureError::new(
            "0/1 knapsack requires at most 20 bounded items with a representable total value",
        ));
    }
    let mut trace = TraceLog::default();
    let result = run_memoization(
        MemoizationProblem::new(
            build_problem(weights, *capacity)?,
            state_id(weights.len(), *capacity),
        )?,
        |node, stored| {
            let (items, current_capacity) = *node.state();
            if items == 0 {
                return Ok(vec![0_i64]);
            }
            let skip = stored
                .get(&state_id(items - 1, current_capacity))
                .copied()
                .ok_or_else(|| StructureError::new("knapsack skip state is absent"))?;
            let weight = weights[items - 1];
            if weight > current_capacity {
                return Ok(vec![skip]);
            }
            let take = stored
                .get(&state_id(items - 1, current_capacity - weight))
                .copied()
                .ok_or_else(|| StructureError::new("knapsack take state is absent"))?
                + values[items - 1];
            Ok(vec![skip, take])
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
            AlgorithmInput::Knapsack {
                weights: vec![1, 3, 4, 5],
                values: vec![1, 4, 5, 7],
                capacity: 7,
            },
        ),
        AlgorithmCase::new(
            "empty",
            AlgorithmInput::Knapsack {
                weights: Vec::new(),
                values: Vec::new(),
                capacity: 10,
            },
        ),
        AlgorithmCase::new(
            "zero-capacity",
            AlgorithmInput::Knapsack {
                weights: vec![1, 2],
                values: vec![4, 7],
                capacity: 0,
            },
        ),
        AlgorithmCase::new(
            "skip-heavy",
            AlgorithmInput::Knapsack {
                weights: vec![5, 6],
                values: vec![10, 12],
                capacity: 4,
            },
        ),
    ];
    let mut generator = generated::Generator::new(68);
    for index in 0..1000 {
        let count = generator.usize(7);
        let weights: Vec<u32> = (0..count).map(|_| 1 + generator.usize(6) as u32).collect();
        let values: Vec<i64> = (0..count).map(|_| generator.i64(0, 12)).collect();
        cases.push(AlgorithmCase::new(
            generated::scenario(index),
            AlgorithmInput::Knapsack {
                weights,
                values,
                capacity: generator.usize(16) as u32,
            },
        ));
    }
    cases
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recurrence_graph_declares_every_candidate_predecessor() {
        let nodes = build_problem(&[2], 3).unwrap();
        let by_id = nodes
            .iter()
            .map(|node| (node.id().to_string(), node))
            .collect::<std::collections::BTreeMap<_, _>>();

        assert_eq!(
            by_id[&state_id(1, 3)].dependencies(),
            &[state_id(0, 3), state_id(0, 1)]
        );
        assert_eq!(by_id[&state_id(1, 1)].dependencies(), &[state_id(0, 1)]);
    }
}
