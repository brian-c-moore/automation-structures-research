use crate::selection::KeyOrder;
use crate::{Structure, StructureError, TraceLog};
use automation_structures::connectives::ordering_pass::IndexArrangement;
use automation_structures::primitives::resource_registry::ResourceRegistry;
use automation_structures::SelectThenActuate as PublishedSelectThenActuate;
use serde::Serialize;

/// Native result of the published selection-to-actuation composition binding.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct SelectionActuationOutcome {
    candidates: Vec<usize>,
    resource: usize,
}

impl SelectionActuationOutcome {
    pub fn candidates(&self) -> &[usize] {
        &self.candidates
    }

    pub fn resource(&self) -> usize {
        self.resource
    }
}

/// One-seat domain binding over the published `SelectThenActuate` composition.
///
/// Candidate positions refer to an immutable ordered subset of resource indices.
/// Published ordering embeds generic minimum keys into the owner's maximum-score
/// policy. Preparation must not mutate through aliases; publication must be a
/// total local assignment. This binding has no crash/remote-effect guarantee or
/// whole-wrapper formal refinement claim.
pub struct SelectThenActuate;

impl SelectThenActuate {
    #[allow(clippy::too_many_arguments)]
    pub fn select_min_and_actuate<T, K: Ord, P>(
        resources: &mut [T],
        candidates: &[usize],
        key: impl Fn(&T) -> K,
        prepare: impl FnOnce(&T, &mut TraceLog, &str) -> Result<P, StructureError>,
        publish: impl FnOnce(&mut T, P),
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<SelectionActuationOutcome, StructureError> {
        if candidates.is_empty() {
            return Err(StructureError::new(
                "select-then-actuate requires at least one candidate",
            ));
        }
        let mut identities = ResourceRegistry::<usize, ()>::new();
        for resource in candidates {
            if *resource >= resources.len() {
                return Err(StructureError::new(format!(
                    "select-then-actuate resource {resource} is out of range"
                )));
            }
            identities
                .try_insert_unique(*resource, ())
                .map_err(|(reason, _, ())| {
                    StructureError::new(format!(
                        "select-then-actuate resource {resource} admission refused: {reason:?}"
                    ))
                })?;
        }

        let mut retained_candidates = Vec::new();
        retained_candidates
            .try_reserve_exact(candidates.len())
            .map_err(|_| StructureError::new("select-then-actuate outcome storage refused"))?;
        retained_candidates.extend_from_slice(candidates);
        let mut keys = Vec::new();
        keys.try_reserve_exact(candidates.len())
            .map_err(|_| StructureError::new("select-then-actuate key storage refused"))?;
        for resource in candidates {
            let target = resources.get(*resource).ok_or_else(|| {
                StructureError::new("select-then-actuate admitted resource is unavailable")
            })?;
            keys.push(key(target));
        }
        let arrangement = IndexArrangement::try_new(keys.len(), &KeyOrder { keys: &keys })
            .map_err(|reason| {
                StructureError::new(format!("candidate ordering refused: {reason:?}"))
            })?;
        let mut owner = PublishedSelectThenActuate::new(1, candidates.len()).map_err(|reason| {
            StructureError::new(format!("select-then-actuate refused: {reason:?}"))
        })?;
        trace.emit(Structure::ActuationPass, "Initialize", subject, "seats=1");
        for (position, rank) in arrangement.inverse().iter().copied().enumerate() {
            let score = candidates
                .len()
                .checked_sub(rank)
                .and_then(|score| u64::try_from(score).ok())
                .ok_or_else(|| StructureError::new("candidate ordinal score is out of range"))?;
            owner.update_score(0, position, score).map_err(|reason| {
                StructureError::new(format!("candidate score refused: {reason:?}"))
            })?;
        }
        trace.emit(
            Structure::CompetitiveSelection,
            "Evaluate",
            subject,
            format!("candidates={}", candidates.len()),
        );
        let winner_position = owner.evaluate(0).map_err(|reason| {
            StructureError::new(format!("candidate selection refused: {reason:?}"))
        })?;
        trace.emit(
            Structure::CompetitiveSelection,
            "Commit",
            subject,
            format!("winner_index={winner_position}"),
        );
        let resource = retained_candidates
            .get(winner_position)
            .copied()
            .ok_or_else(|| {
                StructureError::new("selected candidate is outside the frozen subset")
            })?;
        let target = resources
            .get_mut(resource)
            .ok_or_else(|| StructureError::new("selected resource is unavailable"))?;
        trace.emit(
            Structure::ActuationPass,
            "Check",
            subject,
            format!("seat=0 resource={resource}"),
        );
        let prepared = prepare(target, trace, subject)?;
        owner.actuate(0).map_err(|reason| {
            StructureError::new(format!("selected actuation refused: {reason:?}"))
        })?;
        publish(target, prepared);
        trace.emit(
            Structure::ActuationPass,
            "Commit",
            subject,
            format!("seat=0 resource={resource}"),
        );
        owner.finish().map_err(|reason| {
            StructureError::new(format!("selected closure refused: {reason:?}"))
        })?;
        trace.emit(
            Structure::ActuationPass,
            "Finish",
            subject,
            format!("complete={}", owner.is_complete()),
        );
        Ok(SelectionActuationOutcome {
            candidates: retained_candidates,
            resource,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn applies_the_effect_to_the_selected_resource() -> Result<(), StructureError> {
        let mut trace = TraceLog::default();
        let mut values = [8u64, 3, 5];
        let outcome = SelectThenActuate::select_min_and_actuate(
            &mut values,
            &[0, 1, 2],
            |value| *value,
            |_, _, _| Ok(99),
            |value, prepared| *value = prepared,
            &mut trace,
            "test",
        )?;
        assert_eq!(outcome.resource(), 1);
        assert_eq!(outcome.candidates(), &[0, 1, 2]);
        assert_eq!(values, [8, 99, 5]);
        Ok(())
    }

    #[test]
    fn rejects_duplicate_or_out_of_range_resources() {
        let mut trace = TraceLog::default();
        let mut values = [1u64, 2];
        assert!(SelectThenActuate::select_min_and_actuate(
            &mut values,
            &[0, 0],
            |value| *value,
            |_, _, _| Ok(()),
            |_, ()| {},
            &mut trace,
            "test",
        )
        .is_err());
        assert!(SelectThenActuate::select_min_and_actuate(
            &mut values,
            &[2],
            |value| *value,
            |_, _, _| Ok(()),
            |_, ()| {},
            &mut trace,
            "test",
        )
        .is_err());
        assert_eq!(values, [1, 2]);
    }

    #[test]
    fn stable_subset_order_and_tuple_keys_preserve_actual_resource_identity(
    ) -> Result<(), StructureError> {
        use automation_structures::connectives::counter::Counter;
        use std::cell::Cell;

        let calls = Cell::new(Counter::new(0));
        let mut trace = TraceLog::default();
        // The noncandidate at index 1 has the smallest key. Equal minima at 2/3
        // must resolve by subset order, not by their resource index.
        let mut values = [("z", 9), ("a", 0), ("a", 3), ("a", 3)];
        let outcome = SelectThenActuate::select_min_and_actuate(
            &mut values,
            &[3, 0, 2],
            |value| {
                let mut count = calls.get();
                assert!(count.try_increment());
                calls.set(count);
                *value
            },
            |_, _, _| Ok(("published", 7)),
            |target, prepared| *target = prepared,
            &mut trace,
            "subset",
        )?;
        assert_eq!(outcome.resource(), 3);
        assert_eq!(outcome.candidates(), &[3, 0, 2]);
        assert_eq!(values, [("z", 9), ("a", 0), ("a", 3), ("published", 7)]);
        assert_eq!(calls.get().value(), 3);
        Ok(())
    }

    #[test]
    fn preparation_refusal_changes_no_resource_and_publishes_nothing() {
        use std::cell::Cell;

        let published = Cell::new(false);
        let mut trace = TraceLog::default();
        let mut values = [8u64, 3, 5];
        let result = SelectThenActuate::select_min_and_actuate(
            &mut values,
            &[2, 1],
            |value| *value,
            |_, _, _| Err::<u64, _>(StructureError::new("preparation refused")),
            |target, prepared| {
                published.set(true);
                *target = prepared;
            },
            &mut trace,
            "refusal",
        );
        assert!(result.is_err());
        assert_eq!(values, [8, 3, 5]);
        assert!(!published.get());
        assert_eq!(
            trace.first_sequence(Structure::ActuationPass, "Commit"),
            None
        );
        assert_eq!(
            trace.first_sequence(Structure::ActuationPass, "Finish"),
            None
        );
    }

    #[test]
    fn invalid_subsets_refuse_before_domain_callbacks() {
        use std::cell::Cell;

        for candidates in [&[][..], &[1, 1][..], &[2][..]] {
            let called = Cell::new(false);
            let mut trace = TraceLog::default();
            let mut values = [1u64, 2];
            let result = SelectThenActuate::select_min_and_actuate(
                &mut values,
                candidates,
                |value| {
                    called.set(true);
                    *value
                },
                |_, _, _| {
                    called.set(true);
                    Ok(99)
                },
                |target, prepared| {
                    called.set(true);
                    *target = prepared
                },
                &mut trace,
                "invalid",
            );
            assert!(result.is_err());
            assert!(!called.get());
            assert_eq!(values, [1, 2]);
            assert!(trace.events().is_empty());
        }
    }
}
