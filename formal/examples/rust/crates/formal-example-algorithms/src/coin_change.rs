use crate::{generated, AlgorithmCase, AlgorithmInput, AlgorithmOutput, CompositionResult};
use formal_example_structures::{
    run_memoization, MemoNode, MemoizationControl, MemoizationProblem, StructureError, TraceLog,
};

const UNREACHABLE: i64 = 1_i64 << 60;

fn state_id(amount: u32) -> String {
    format!("amount-{amount:05}")
}

pub(crate) fn build_problem(
    coins: &[u32],
    amount: u32,
) -> Result<Vec<MemoNode<u32>>, StructureError> {
    (0..=amount)
        .map(|value| {
            let dependencies = if value == 0 {
                Vec::new()
            } else {
                coins
                    .iter()
                    .filter(|coin| **coin <= value)
                    .map(|coin| state_id(value - *coin))
                    .collect()
            };
            MemoNode::new(state_id(value), dependencies, value)
        })
        .collect()
}

pub(crate) fn compose(
    input: &AlgorithmInput,
    scope: &str,
    control: MemoizationControl,
) -> Result<CompositionResult, StructureError> {
    let AlgorithmInput::CoinChange { coins, amount } = input else {
        return Err(StructureError::new(
            "coin change requires coins and an amount",
        ));
    };
    if coins.is_empty() || coins.contains(&0) || *amount > 10_000 {
        return Err(StructureError::new(
            "coin change requires positive coins and an amount at most 10000",
        ));
    }
    let mut trace = TraceLog::default();
    let result = run_memoization(
        MemoizationProblem::new(build_problem(coins, *amount)?, state_id(*amount))?,
        |node, stored| {
            if *node.state() == 0 {
                return Ok(vec![0_i64]);
            }
            if node.dependencies().is_empty() {
                return Ok(vec![UNREACHABLE]);
            }
            node.dependencies()
                .iter()
                .map(|dependency| {
                    let prior = stored.get(dependency).copied().ok_or_else(|| {
                        StructureError::new(format!(
                            "coin-change dependency {dependency} is absent"
                        ))
                    })?;
                    Ok(if prior >= UNREACHABLE {
                        UNREACHABLE
                    } else {
                        prior + 1
                    })
                })
                .collect()
        },
        UNREACHABLE,
        i64::min,
        &mut trace,
        scope,
        control,
    )?;
    let output = if result.result >= UNREACHABLE {
        -1
    } else {
        result.result
    };
    Ok(CompositionResult {
        output: AlgorithmOutput::Integer(output),
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
            AlgorithmInput::CoinChange {
                coins: vec![1, 2, 5],
                amount: 11,
            },
        ),
        AlgorithmCase::new(
            "unreachable",
            AlgorithmInput::CoinChange {
                coins: vec![2],
                amount: 3,
            },
        ),
        AlgorithmCase::new(
            "zero-amount",
            AlgorithmInput::CoinChange {
                coins: vec![1],
                amount: 0,
            },
        ),
        AlgorithmCase::new(
            "noncanonical",
            AlgorithmInput::CoinChange {
                coins: vec![3, 4],
                amount: 6,
            },
        ),
    ];
    let sets = [vec![1, 2, 5], vec![2, 3, 7], vec![1, 5, 10, 25], vec![3, 4]];
    let mut generator = generated::Generator::new(63);
    for index in 0..1000 {
        cases.push(AlgorithmCase::new(
            generated::scenario(index),
            AlgorithmInput::CoinChange {
                coins: sets[generator.usize(sets.len())].clone(),
                amount: generator.usize(41) as u32,
            },
        ));
    }
    cases
}
