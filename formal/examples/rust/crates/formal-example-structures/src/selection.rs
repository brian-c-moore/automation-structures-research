use crate::{Structure, StructureError, TraceLog};

pub struct CompetitiveSelection;

impl CompetitiveSelection {
    pub fn select_min_index<T, K: Ord>(
        candidates: &[T],
        key: impl Fn(&T) -> K,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<usize, StructureError> {
        trace.emit(
            Structure::CompetitiveSelection,
            "Evaluate",
            subject,
            format!("candidates={}", candidates.len()),
        );
        let mut best: Option<(usize, K)> = None;
        for (index, candidate) in candidates.iter().enumerate() {
            let candidate_key = key(candidate);
            if best
                .as_ref()
                .map(|(_, best_key)| candidate_key < *best_key)
                .unwrap_or(true)
            {
                best = Some((index, candidate_key));
            }
        }
        let index = best
            .map(|(index, _)| index)
            .ok_or_else(|| StructureError::new("competitive selection has no candidate"))?;
        trace.emit(
            Structure::CompetitiveSelection,
            "Commit",
            subject,
            format!("winner_index={index}"),
        );
        Ok(index)
    }

    pub fn select_min_indices<T, K: Ord>(
        candidates: &[T],
        key: impl Fn(&T) -> K,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<Vec<usize>, StructureError> {
        trace.emit(
            Structure::CompetitiveSelection,
            "Evaluate",
            subject,
            format!("candidates={}", candidates.len()),
        );
        let mut best_key = None;
        let mut winners = Vec::new();
        for (index, candidate) in candidates.iter().enumerate() {
            let candidate_key = key(candidate);
            match best_key.as_ref() {
                None => {
                    best_key = Some(candidate_key);
                    winners.push(index);
                }
                Some(current) if candidate_key < *current => {
                    best_key = Some(candidate_key);
                    winners.clear();
                    winners.push(index);
                }
                Some(current) if candidate_key == *current => winners.push(index),
                Some(_) => {}
            }
        }
        trace.emit(
            Structure::CompetitiveSelection,
            "Commit",
            subject,
            format!("winners={}", winners.len()),
        );
        Ok(winners)
    }
}
