use crate::{AlgorithmInput, AlgorithmOutput};
use std::collections::{BTreeSet, VecDeque};

pub fn memoization_fixture() -> AlgorithmOutput {
    AlgorithmOutput::Integer(2 + 3)
}

pub fn climbing_stairs(input: &AlgorithmInput) -> Result<AlgorithmOutput, String> {
    let AlgorithmInput::Steps { steps } = input else {
        return Err("climbing stairs requires a step count".to_string());
    };
    let (mut previous, mut current) = (1_i64, 1_i64);
    for _ in 0..*steps {
        (previous, current) = (current, previous + current);
    }
    Ok(AlgorithmOutput::Integer(previous))
}

pub fn house_robber(input: &AlgorithmInput) -> Result<AlgorithmOutput, String> {
    let AlgorithmInput::Numbers { values } = input else {
        return Err("house robber requires a number list".to_string());
    };
    let (mut take, mut skip) = (0_i64, 0_i64);
    for value in values {
        (take, skip) = (skip + value, take.max(skip));
    }
    Ok(AlgorithmOutput::Integer(take.max(skip)))
}

pub fn longest_increasing_subsequence(input: &AlgorithmInput) -> Result<AlgorithmOutput, String> {
    let AlgorithmInput::Numbers { values } = input else {
        return Err("longest increasing subsequence requires a number list".to_string());
    };
    let mut tails: Vec<i64> = Vec::new();
    for value in values {
        let index = tails.partition_point(|tail| tail < value);
        if index == tails.len() {
            tails.push(*value);
        } else {
            tails[index] = *value;
        }
    }
    Ok(AlgorithmOutput::Integer(tails.len() as i64))
}

pub fn coin_change(input: &AlgorithmInput) -> Result<AlgorithmOutput, String> {
    let AlgorithmInput::CoinChange { coins, amount } = input else {
        return Err("coin change requires coins and an amount".to_string());
    };
    let mut distance = vec![None; *amount as usize + 1];
    let mut queue = VecDeque::from([0_u32]);
    distance[0] = Some(0_i64);
    while let Some(total) = queue.pop_front() {
        let steps = distance[total as usize].expect("queued total has a distance");
        for coin in coins {
            let next = total.saturating_add(*coin);
            if next <= *amount && distance[next as usize].is_none() {
                distance[next as usize] = Some(steps + 1);
                queue.push_back(next);
            }
        }
    }
    Ok(AlgorithmOutput::Integer(
        distance[*amount as usize].unwrap_or(-1),
    ))
}

pub fn word_break(input: &AlgorithmInput) -> Result<AlgorithmOutput, String> {
    let AlgorithmInput::WordBreak { text, dictionary } = input else {
        return Err("word break requires text and a dictionary".to_string());
    };
    let characters: Vec<char> = text.chars().collect();
    let words: BTreeSet<Vec<char>> = dictionary
        .iter()
        .map(|word| word.chars().collect())
        .collect();
    let mut queue = VecDeque::from([0_usize]);
    let mut visited = BTreeSet::from([0_usize]);
    while let Some(start) = queue.pop_front() {
        if start == characters.len() {
            return Ok(AlgorithmOutput::Boolean(true));
        }
        for end in start + 1..=characters.len() {
            if words.contains(&characters[start..end]) && visited.insert(end) {
                queue.push_back(end);
            }
        }
    }
    Ok(AlgorithmOutput::Boolean(false))
}

pub fn unique_paths(input: &AlgorithmInput) -> Result<AlgorithmOutput, String> {
    let AlgorithmInput::Grid { rows, columns } = input else {
        return Err("unique paths requires grid dimensions".to_string());
    };
    if *rows == 0 || *columns == 0 {
        return Err("unique paths dimensions must be positive".to_string());
    }
    let down = u64::from(*rows - 1);
    let right = u64::from(*columns - 1);
    let choose = down.min(right);
    let total = down + right;
    let mut result = 1_u128;
    for index in 1..=choose {
        result = result * u128::from(total - choose + index) / u128::from(index);
    }
    let result = i64::try_from(result)
        .map_err(|_| "unique paths result does not fit the registered output".to_string())?;
    Ok(AlgorithmOutput::Integer(result))
}

pub fn longest_common_subsequence(input: &AlgorithmInput) -> Result<AlgorithmOutput, String> {
    let AlgorithmInput::TextPair { left, right } = input else {
        return Err("longest common subsequence requires two strings".to_string());
    };
    let left: Vec<char> = left.chars().collect();
    let right: Vec<char> = right.chars().collect();
    let mut row = vec![0_i64; right.len() + 1];
    for left_char in left {
        let mut diagonal = 0_i64;
        for (index, right_char) in right.iter().enumerate() {
            let prior = row[index + 1];
            row[index + 1] = if left_char == *right_char {
                diagonal + 1
            } else {
                row[index + 1].max(row[index])
            };
            diagonal = prior;
        }
    }
    Ok(AlgorithmOutput::Integer(row[right.len()]))
}

pub fn edit_distance(input: &AlgorithmInput) -> Result<AlgorithmOutput, String> {
    let AlgorithmInput::TextPair { left, right } = input else {
        return Err("edit distance requires two strings".to_string());
    };
    let left: Vec<char> = left.chars().collect();
    let right: Vec<char> = right.chars().collect();
    let mut row: Vec<i64> = (0..=right.len()).map(|value| value as i64).collect();
    for (left_index, left_char) in left.iter().enumerate() {
        let mut diagonal = row[0];
        row[0] = left_index as i64 + 1;
        for (right_index, right_char) in right.iter().enumerate() {
            let prior = row[right_index + 1];
            row[right_index + 1] = if left_char == right_char {
                diagonal
            } else {
                1 + diagonal.min(row[right_index]).min(row[right_index + 1])
            };
            diagonal = prior;
        }
    }
    Ok(AlgorithmOutput::Integer(row[right.len()]))
}

pub fn knapsack_01(input: &AlgorithmInput) -> Result<AlgorithmOutput, String> {
    let AlgorithmInput::Knapsack {
        weights,
        values,
        capacity,
    } = input
    else {
        return Err("0/1 knapsack requires weights, values, and capacity".to_string());
    };
    if weights.len() != values.len() {
        return Err("0/1 knapsack weights and values differ in length".to_string());
    }
    let mut best = 0_i64;
    for mask in 0_u64..(1_u64 << weights.len()) {
        let mut weight = 0_u32;
        let mut value = 0_i64;
        for index in 0..weights.len() {
            if mask & (1_u64 << index) != 0 {
                weight += weights[index];
                value += values[index];
            }
        }
        if weight <= *capacity {
            best = best.max(value);
        }
    }
    Ok(AlgorithmOutput::Integer(best))
}

pub fn longest_palindromic_subsequence(input: &AlgorithmInput) -> Result<AlgorithmOutput, String> {
    let AlgorithmInput::Text { text } = input else {
        return Err("longest palindromic subsequence requires text".to_string());
    };
    let reversed: String = text.chars().rev().collect();
    longest_common_subsequence(&AlgorithmInput::TextPair {
        left: text.clone(),
        right: reversed,
    })
}

pub fn evaluate(id: &str, input: &AlgorithmInput) -> Result<AlgorithmOutput, String> {
    match id {
        "FEX-ALG-060" => climbing_stairs(input),
        "FEX-ALG-061" => house_robber(input),
        "FEX-ALG-062" => longest_increasing_subsequence(input),
        "FEX-ALG-063" => coin_change(input),
        "FEX-ALG-064" => word_break(input),
        "FEX-ALG-065" => unique_paths(input),
        "FEX-ALG-066" => longest_common_subsequence(input),
        "FEX-ALG-067" => edit_distance(input),
        "FEX-ALG-068" => knapsack_01(input),
        "FEX-ALG-069" => longest_palindromic_subsequence(input),
        _ => Err(format!("unknown Memoization algorithm {id}")),
    }
}
