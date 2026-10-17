use crate::{Structure, StructureError, TraceLog};
use automation_structures::connectives::ordering_pass::PositionOrder;
use automation_structures::primitives::competitive_selection::CompetitiveSelectionMinimum;

// Immutable domain keys; the published profile owns arrangement and selection.
pub(crate) struct KeyOrder<'a, K> {
    pub(crate) keys: &'a [K],
}

impl<K: Ord> PositionOrder for KeyOrder<'_, K> {
    fn len(&self) -> usize {
        self.keys.len()
    }

    fn compare(&self, left: usize, right: usize) -> i8 {
        match self.keys.get(left).cmp(&self.keys.get(right)) {
            std::cmp::Ordering::Less => -1,
            std::cmp::Ordering::Equal => 0,
            std::cmp::Ordering::Greater => 1,
        }
    }
}

fn project_keys<T, K>(candidates: &[T], key: impl Fn(&T) -> K) -> Result<Vec<K>, StructureError> {
    let mut keys = Vec::new();
    keys.try_reserve_exact(candidates.len())
        .map_err(|_| StructureError::new("competitive selection key storage refused"))?;
    keys.extend(candidates.iter().map(key));
    Ok(keys)
}

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
        let keys = project_keys(candidates, key)?;
        let owner = CompetitiveSelectionMinimum::try_new(KeyOrder { keys: &keys })
            .map_err(|_| StructureError::new("competitive selection arrangement refused"))?;
        let index = owner
            .selected()
            .first()
            .copied()
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
        let keys = project_keys(candidates, key)?;
        let owner = CompetitiveSelectionMinimum::try_new(KeyOrder { keys: &keys })
            .map_err(|_| StructureError::new("competitive selection arrangement refused"))?;
        let mut winners = Vec::new();
        winners
            .try_reserve_exact(owner.len())
            .map_err(|_| StructureError::new("competitive selection result storage refused"))?;
        winners.extend_from_slice(owner.selected());
        trace.emit(
            Structure::CompetitiveSelection,
            "Commit",
            subject,
            format!("winners={}", winners.len()),
        );
        Ok(winners)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use automation_structures::connectives::counter::Counter;
    use std::cell::Cell;

    #[test]
    fn preserves_stable_ties_and_one_key_evaluation_per_candidate() -> Result<(), StructureError> {
        let calls = Cell::new(Counter::new(0));
        let values = [9, 2, 2, 4, 2];
        let mut trace = TraceLog::default();
        let winners = CompetitiveSelection::select_min_indices(
            &values,
            |value| {
                let mut count = calls.get();
                assert!(count.try_increment());
                calls.set(count);
                *value
            },
            &mut trace,
            "stable-minimum",
        )?;
        assert_eq!(winners, vec![1, 2, 4]);
        assert_eq!(
            usize::try_from(calls.get().value()).ok(),
            Some(values.len())
        );
        assert_eq!(
            CompetitiveSelection::select_min_index(
                &values,
                |value| *value,
                &mut trace,
                "first-minimum"
            )?,
            1
        );
        Ok(())
    }

    #[test]
    fn preserves_empty_singular_refusal_and_empty_plural_result() -> Result<(), StructureError> {
        let values: [u64; 0] = [];
        let mut trace = TraceLog::default();
        assert!(CompetitiveSelection::select_min_index(
            &values,
            |value| *value,
            &mut trace,
            "empty"
        )
        .is_err());
        assert!(CompetitiveSelection::select_min_indices(
            &values,
            |value| *value,
            &mut trace,
            "empty"
        )?
        .is_empty());
        Ok(())
    }
}
