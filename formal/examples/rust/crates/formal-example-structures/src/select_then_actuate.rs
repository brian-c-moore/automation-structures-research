use crate::{ActuationPass, CompetitiveSelection, StructureError, TraceLog};
use serde::Serialize;
use std::collections::BTreeSet;

/// Result of the verified selection-to-actuation handoff.
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

/// One-shot readable specialization of the shared-allocation contract in
/// `formal/composition/structure-compositions/SelectThenActuate.tla`.
///
/// The full state-machine witness remains in
/// `crate://automation-structures/0.2.3/src/compositions/select_then_actuate.rs`. This
/// adapter composes the readable `CompetitiveSelection` and `ActuationPass`
/// donors for examples that evaluate and actuate one seat in one call.
pub struct SelectThenActuate;

impl SelectThenActuate {
    pub fn select_min_and_actuate<T, K: Ord>(
        resources: &mut [T],
        candidates: &[usize],
        key: impl Fn(&T) -> K,
        operation: impl FnOnce(&mut T, &mut TraceLog, &str) -> Result<(), StructureError>,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<SelectionActuationOutcome, StructureError> {
        if candidates.is_empty() {
            return Err(StructureError::new(
                "select-then-actuate requires at least one candidate",
            ));
        }
        let mut identities = BTreeSet::new();
        for resource in candidates {
            if *resource >= resources.len() {
                return Err(StructureError::new(format!(
                    "select-then-actuate resource {resource} is out of range"
                )));
            }
            if !identities.insert(*resource) {
                return Err(StructureError::new(format!(
                    "select-then-actuate resource {resource} is duplicated"
                )));
            }
        }

        let winner_position = CompetitiveSelection::select_min_index(
            candidates,
            |resource| key(&resources[*resource]),
            trace,
            subject,
        )?;
        let resource = candidates[winner_position];
        let mut actuation = ActuationPass::new(vec![Some(resource)], trace, subject);
        actuation.actuate_with(0, resources, operation, trace, subject)?;
        actuation.finish(trace, subject)?;
        if actuation.allocation() != actuation.effects() {
            return Err(StructureError::new(
                "select-then-actuate effect does not match the selected allocation",
            ));
        }
        Ok(SelectionActuationOutcome {
            candidates: candidates.to_vec(),
            resource,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn applies_the_effect_to_the_selected_resource() {
        let mut trace = TraceLog::default();
        let mut values = [8u64, 3, 5];
        let outcome = SelectThenActuate::select_min_and_actuate(
            &mut values,
            &[0, 1, 2],
            |value| *value,
            |value, _, _| {
                *value = 99;
                Ok(())
            },
            &mut trace,
            "test",
        )
        .unwrap();
        assert_eq!(outcome.resource(), 1);
        assert_eq!(outcome.candidates(), &[0, 1, 2]);
        assert_eq!(values, [8, 99, 5]);
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
            &mut trace,
            "test",
        )
        .is_err());
        assert!(SelectThenActuate::select_min_and_actuate(
            &mut values,
            &[2],
            |value| *value,
            |_, _, _| Ok(()),
            &mut trace,
            "test",
        )
        .is_err());
    }
}
