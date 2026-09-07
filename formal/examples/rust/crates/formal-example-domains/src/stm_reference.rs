use crate::stm::{TransactionRecord, TransactionStatus, TxnOperation};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OpacityEvaluation {
    pub accepted: bool,
    pub serialization: Vec<String>,
    pub final_heap: BTreeMap<String, i64>,
}

/// Exhaustive value-level opacity reference for the registered finite history.
///
/// The evaluator imports no shared structures and reads no construction trace,
/// epoch state, read set, write buffer, or actuation state. It enumerates every
/// transaction order that respects observed real-time precedence. Committed,
/// aborted, and incomplete transactions must all read from one legal serial
/// state; only committed writes enter the final heap.
pub fn evaluate_opacity(
    initial_heap: &BTreeMap<String, i64>,
    final_heap: &BTreeMap<String, i64>,
    transactions: &[TransactionRecord],
) -> OpacityEvaluation {
    let mut indices = (0..transactions.len()).collect::<Vec<_>>();
    let mut permutations = Vec::new();
    enumerate_permutations(&mut indices, 0, &mut permutations);
    for order in permutations {
        if !respects_real_time(&order, transactions) {
            continue;
        }
        if let Some(replayed) = replay_order(initial_heap, &order, transactions) {
            if &replayed == final_heap {
                return OpacityEvaluation {
                    accepted: true,
                    serialization: order
                        .into_iter()
                        .map(|index| transactions[index].id.clone())
                        .collect(),
                    final_heap: replayed,
                };
            }
        }
    }
    OpacityEvaluation {
        accepted: false,
        serialization: Vec::new(),
        final_heap: final_heap.clone(),
    }
}

fn enumerate_permutations(values: &mut [usize], start: usize, output: &mut Vec<Vec<usize>>) {
    if start == values.len() {
        output.push(values.to_vec());
        return;
    }
    for index in start..values.len() {
        values.swap(start, index);
        enumerate_permutations(values, start + 1, output);
        values.swap(start, index);
    }
}

fn respects_real_time(order: &[usize], transactions: &[TransactionRecord]) -> bool {
    let positions = order
        .iter()
        .enumerate()
        .map(|(position, index)| (*index, position))
        .collect::<BTreeMap<_, _>>();
    for (left_index, left) in transactions.iter().enumerate() {
        let Some(left_end) = left.end_sequence else {
            continue;
        };
        for (right_index, right) in transactions.iter().enumerate() {
            if left_end < right.begin_sequence && positions[&left_index] >= positions[&right_index]
            {
                return false;
            }
        }
    }
    true
}

fn replay_order(
    initial_heap: &BTreeMap<String, i64>,
    order: &[usize],
    transactions: &[TransactionRecord],
) -> Option<BTreeMap<String, i64>> {
    let mut heap = initial_heap.clone();
    for index in order {
        let transaction = &transactions[*index];
        let mut local_writes = BTreeMap::new();
        let mut sequences = BTreeSet::new();
        for operation in &transaction.operations {
            if !sequences.insert(operation.sequence()) {
                return None;
            }
            match operation {
                TxnOperation::Read {
                    cell,
                    value,
                    sequence: _,
                } => {
                    let expected = local_writes.get(cell).or_else(|| heap.get(cell))?;
                    if expected != value {
                        return None;
                    }
                }
                TxnOperation::Write {
                    cell,
                    value,
                    sequence: _,
                } => {
                    if !heap.contains_key(cell) {
                        return None;
                    }
                    local_writes.insert(cell.clone(), *value);
                }
            }
        }
        if transaction.status == TransactionStatus::Committed {
            for (cell, value) in local_writes {
                heap.insert(cell, value);
            }
        }
    }
    Some(heap)
}
