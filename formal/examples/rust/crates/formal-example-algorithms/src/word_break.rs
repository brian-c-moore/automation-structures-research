use crate::{generated, AlgorithmCase, AlgorithmInput, AlgorithmOutput, CompositionResult};
use formal_example_structures::{
    run_memoization, MemoNode, MemoizationControl, MemoizationProblem, StructureError, TraceLog,
};
use std::collections::BTreeSet;

fn state_id(offset: usize) -> String {
    format!("offset-{offset:04}")
}

pub(crate) fn build_problem(
    characters: &[char],
    dictionary: &BTreeSet<Vec<char>>,
) -> Result<Vec<MemoNode<usize>>, StructureError> {
    (0..=characters.len())
        .map(|end| {
            let dependencies = if end == 0 {
                Vec::new()
            } else {
                (0..end)
                    .filter(|start| dictionary.contains(&characters[*start..end]))
                    .map(state_id)
                    .collect()
            };
            MemoNode::new(state_id(end), dependencies, end)
        })
        .collect()
}

pub(crate) fn compose(
    input: &AlgorithmInput,
    scope: &str,
    control: MemoizationControl,
) -> Result<CompositionResult, StructureError> {
    let AlgorithmInput::WordBreak { text, dictionary } = input else {
        return Err(StructureError::new(
            "word break requires text and a dictionary",
        ));
    };
    if text.chars().count() > 300
        || dictionary.is_empty()
        || dictionary.iter().any(|word| word.is_empty())
    {
        return Err(StructureError::new(
            "word break requires bounded text and a nonempty dictionary of nonempty words",
        ));
    }
    let characters: Vec<char> = text.chars().collect();
    let words: BTreeSet<Vec<char>> = dictionary
        .iter()
        .map(|word| word.chars().collect())
        .collect();
    let mut trace = TraceLog::default();
    let result = run_memoization(
        MemoizationProblem::new(
            build_problem(&characters, &words)?,
            state_id(characters.len()),
        )?,
        |node, stored| {
            if *node.state() == 0 {
                return Ok(vec![true]);
            }
            let mut candidates = vec![false];
            for dependency in node.dependencies() {
                candidates.push(stored.get(dependency).copied().ok_or_else(|| {
                    StructureError::new(format!("word-break dependency {dependency} is absent"))
                })?);
            }
            Ok(candidates)
        },
        false,
        |left, right| left || right,
        &mut trace,
        scope,
        control,
    )?;
    Ok(CompositionResult {
        output: AlgorithmOutput::Boolean(result.result),
        trace,
        admitted_states: result.admitted_states,
        stored_states: result.stored_states,
        scope: scope.to_string(),
    })
}

fn dictionary(words: &[&str]) -> Vec<String> {
    words.iter().map(|word| (*word).to_string()).collect()
}

pub(crate) fn cases() -> Vec<AlgorithmCase> {
    let fixed = dictionary(&["a", "b", "c", "ab", "bc", "abc", "ca"]);
    let mut cases = vec![
        AlgorithmCase::new(
            "baseline",
            AlgorithmInput::WordBreak {
                text: "leetcode".to_string(),
                dictionary: dictionary(&["leet", "code"]),
            },
        ),
        AlgorithmCase::new(
            "reused-word",
            AlgorithmInput::WordBreak {
                text: "applepenapple".to_string(),
                dictionary: dictionary(&["apple", "pen"]),
            },
        ),
        AlgorithmCase::new(
            "unsegmentable",
            AlgorithmInput::WordBreak {
                text: "catsandog".to_string(),
                dictionary: dictionary(&["cats", "dog", "sand", "and", "cat"]),
            },
        ),
        AlgorithmCase::new(
            "empty-text",
            AlgorithmInput::WordBreak {
                text: String::new(),
                dictionary: fixed.clone(),
            },
        ),
    ];
    let mut generator = generated::Generator::new(64);
    for index in 0..1000 {
        cases.push(AlgorithmCase::new(
            generated::scenario(index),
            AlgorithmInput::WordBreak {
                text: generator.text(8, 3),
                dictionary: fixed.clone(),
            },
        ));
    }
    cases
}
