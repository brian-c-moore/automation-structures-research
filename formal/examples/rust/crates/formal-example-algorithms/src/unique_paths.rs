use crate::{generated, AlgorithmCase, AlgorithmInput, AlgorithmOutput, CompositionResult};
use formal_example_structures::{
    run_memoization, MemoNode, MemoizationControl, MemoizationProblem, StructureError, TraceLog,
};

fn state_id(row: u32, column: u32) -> String {
    format!("cell-{row:03}-{column:03}")
}

pub(crate) fn build_problem(
    rows: u32,
    columns: u32,
) -> Result<Vec<MemoNode<(u32, u32)>>, StructureError> {
    let mut nodes = Vec::new();
    for row in 0..rows {
        for column in 0..columns {
            let mut dependencies = Vec::new();
            if row > 0 {
                dependencies.push(state_id(row - 1, column));
            }
            if column > 0 {
                dependencies.push(state_id(row, column - 1));
            }
            nodes.push(MemoNode::new(
                state_id(row, column),
                dependencies,
                (row, column),
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
    let AlgorithmInput::Grid { rows, columns } = input else {
        return Err(StructureError::new("unique paths requires grid dimensions"));
    };
    if *rows == 0 || *columns == 0 || *rows > 100 || *columns > 100 || *rows + *columns > 68 {
        return Err(StructureError::new(
            "unique paths requires dimensions from 1 through 100 with a sum at most 68",
        ));
    }
    let mut trace = TraceLog::default();
    let result = run_memoization(
        MemoizationProblem::new(
            build_problem(*rows, *columns)?,
            state_id(*rows - 1, *columns - 1),
        )?,
        |node, stored| {
            let (row, column) = *node.state();
            if row == 0 || column == 0 {
                return Ok(vec![1_i64]);
            }
            node.dependencies()
                .iter()
                .map(|dependency| {
                    stored.get(dependency).copied().ok_or_else(|| {
                        StructureError::new(format!(
                            "unique-paths dependency {dependency} is absent"
                        ))
                    })
                })
                .collect()
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
        AlgorithmCase::new(
            "baseline",
            AlgorithmInput::Grid {
                rows: 3,
                columns: 7,
            },
        ),
        AlgorithmCase::new(
            "single-cell",
            AlgorithmInput::Grid {
                rows: 1,
                columns: 1,
            },
        ),
        AlgorithmCase::new(
            "single-row",
            AlgorithmInput::Grid {
                rows: 1,
                columns: 8,
            },
        ),
        AlgorithmCase::new(
            "rectangular",
            AlgorithmInput::Grid {
                rows: 3,
                columns: 2,
            },
        ),
    ];
    let mut generator = generated::Generator::new(65);
    for index in 0..1000 {
        cases.push(AlgorithmCase::new(
            generated::scenario(index),
            AlgorithmInput::Grid {
                rows: 1 + generator.usize(8) as u32,
                columns: 1 + generator.usize(8) as u32,
            },
        ));
    }
    cases
}
