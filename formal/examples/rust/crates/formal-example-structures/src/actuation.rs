use crate::{Structure, StructureError, TraceLog};
use automation_structures::ActuationPass as PublishedActuationPass;

/// Trace adapter over the published `ActuationPass` implementation.
///
/// Transition admission and carrier state are owned by
/// the published `automation_structures::ActuationPass` facade and its carrier.
pub struct ActuationPass {
    inner: PublishedActuationPass,
}

impl ActuationPass {
    pub fn new(allocation: Vec<Option<usize>>, trace: &mut TraceLog, subject: &str) -> Self {
        trace.emit(
            Structure::ActuationPass,
            "Initialize",
            subject,
            format!("seats={}", allocation.len()),
        );
        let allocation = allocation
            .into_iter()
            .map(|entry| entry.map(|resource| resource as u64))
            .collect();
        Self {
            inner: PublishedActuationPass::new(allocation),
        }
    }

    pub fn allocation(&self) -> &[Option<u64>] {
        self.inner.allocations()
    }

    pub fn effects(&self) -> &[Option<u64>] {
        self.inner.effects()
    }

    pub fn is_complete(&self) -> bool {
        self.inner.is_complete()
    }

    pub fn allocate(
        &mut self,
        seat: usize,
        resource: usize,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<(), StructureError> {
        self.inner
            .allocate(seat, resource as u64)
            .map_err(|error| structure_error("allocate", error))?;
        trace.emit(
            Structure::ActuationPass,
            "Allocate",
            subject,
            format!("seat={seat} resource={resource}"),
        );
        Ok(())
    }

    pub fn deallocate(
        &mut self,
        seat: usize,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<(), StructureError> {
        self.inner
            .deallocate(seat)
            .map_err(|error| structure_error("deallocate", error))?;
        trace.emit(
            Structure::ActuationPass,
            "Deallocate",
            subject,
            format!("seat={seat}"),
        );
        Ok(())
    }

    pub fn actuate(
        &mut self,
        seat: usize,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<usize, StructureError> {
        let resource = self.inner.allocation(seat).flatten().ok_or_else(|| {
            StructureError::new(format!("actuation seat {seat} is not allocated"))
        })?;
        trace.emit(
            Structure::ActuationPass,
            "Check",
            subject,
            format!("seat={seat} resource={resource}"),
        );
        self.inner
            .actuate(seat)
            .map_err(|error| structure_error("actuate", error))?;
        trace.emit(
            Structure::ActuationPass,
            "Commit",
            subject,
            format!("seat={seat} resource={resource}"),
        );
        usize::try_from(resource)
            .map_err(|_| StructureError::new("actuation resource does not fit usize"))
    }

    /// Prepare against an immutable target, then publish under the same exclusive borrow.
    /// Preparation must not mutate through aliases/captures; publication must be total
    /// domain wiring. This does not provide crash or remote transaction recovery.
    #[allow(clippy::too_many_arguments)]
    pub fn actuate_with<T, P>(
        &mut self,
        seat: usize,
        resources: &mut [T],
        prepare: impl FnOnce(&T, &mut TraceLog, &str) -> Result<P, StructureError>,
        publish: impl FnOnce(&mut T, P),
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<usize, StructureError> {
        if self.inner.is_complete() || self.inner.effect(seat).flatten().is_some() {
            return Err(StructureError::new(format!(
                "actuation seat {seat} cannot accept another effect"
            )));
        }
        let resource = self.inner.allocation(seat).flatten().ok_or_else(|| {
            StructureError::new(format!("actuation seat {seat} is not allocated"))
        })?;
        let resource = usize::try_from(resource)
            .map_err(|_| StructureError::new("actuation resource does not fit usize"))?;
        let target = resources.get_mut(resource).ok_or_else(|| {
            StructureError::new(format!(
                "actuation resource {resource} is outside the supplied resource set"
            ))
        })?;
        trace.emit(
            Structure::ActuationPass,
            "Check",
            subject,
            format!("seat={seat} resource={resource}"),
        );
        let prepared = prepare(target, trace, subject)?;
        self.inner
            .actuate(seat)
            .map_err(|error| structure_error("actuate", error))?;
        publish(target, prepared);
        trace.emit(
            Structure::ActuationPass,
            "Commit",
            subject,
            format!("seat={seat} resource={resource}"),
        );
        Ok(resource)
    }

    pub fn finish(&mut self, trace: &mut TraceLog, subject: &str) -> Result<(), StructureError> {
        self.inner
            .finish()
            .map_err(|error| structure_error("finish", error))?;
        trace.emit(
            Structure::ActuationPass,
            "Finish",
            subject,
            format!("complete={}", self.inner.is_complete()),
        );
        Ok(())
    }
}

impl Clone for ActuationPass {
    fn clone(&self) -> Self {
        let mut inner = PublishedActuationPass::new(self.inner.allocations().to_vec());
        for (seat, effect) in self.inner.effects().iter().enumerate() {
            if effect.is_some() {
                inner
                    .actuate(seat)
                    .expect("published actuation observation must replay");
            }
        }
        if self.inner.is_complete() {
            inner
                .finish()
                .expect("published completed actuation must replay");
        }
        Self { inner }
    }
}

impl core::fmt::Debug for ActuationPass {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("ActuationPass")
            .field("allocation", &self.inner.allocations())
            .field("effects", &self.inner.effects())
            .field("complete", &self.inner.is_complete())
            .finish()
    }
}

fn structure_error(action: &str, error: automation_structures::ActuationError) -> StructureError {
    StructureError::new(format!(
        "published ActuationPass rejected {action}: {error}"
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preparation_refusal_preserves_live_target_and_allows_retry() -> Result<(), StructureError> {
        let mut trace = TraceLog::default();
        let mut resources = [String::from("original")];
        let mut pass = ActuationPass::new(vec![Some(0)], &mut trace, "staged");
        let refused = pass.actuate_with(
            0,
            &mut resources,
            |value, _, _| -> Result<String, StructureError> {
                let mut staged = value.clone();
                staged.push_str(" modified");
                Err(StructureError::new(format!("refused {staged}")))
            },
            |value, staged| *value = staged,
            &mut trace,
            "staged",
        );
        assert!(refused.is_err());
        assert_eq!(resources, ["original"]);
        assert_eq!(pass.effects(), &[None]);
        assert!(!trace.events().iter().any(|event| event.action == "Commit"));
        pass.actuate_with(
            0,
            &mut resources,
            |_, _, _| Ok(String::from("accepted")),
            |value, staged| *value = staged,
            &mut trace,
            "staged",
        )?;
        assert_eq!(resources, ["accepted"]);
        assert_eq!(pass.effects(), &[Some(0)]);
        let called = std::cell::Cell::new(false);
        let forbidden = |_: &String, _: &mut TraceLog, _: &str| -> Result<String, StructureError> {
            called.set(true);
            Ok(String::new())
        };
        assert!(pass
            .actuate_with(
                0,
                &mut resources,
                forbidden,
                |_, _| {},
                &mut trace,
                "staged"
            )
            .is_err());
        pass.finish(&mut trace, "staged")?;
        assert!(pass
            .actuate_with(
                0,
                &mut resources,
                forbidden,
                |_, _| {},
                &mut trace,
                "staged"
            )
            .is_err());
        assert_eq!(resources, ["accepted"]);
        assert!(!called.get());
        Ok(())
    }

    #[test]
    fn invalid_target_refuses_before_preparation() {
        let mut trace = TraceLog::default();
        let mut resources = [0u64];
        let mut pass = ActuationPass::new(vec![Some(1), None], &mut trace, "invalid");
        for seat in [0, 1, 2] {
            let calls = std::cell::Cell::new(false);
            assert!(pass
                .actuate_with(
                    seat,
                    &mut resources,
                    |_, _, _| {
                        calls.set(true);
                        Ok(9)
                    },
                    |value, prepared| *value = prepared,
                    &mut trace,
                    "invalid"
                )
                .is_err());
            assert!(!calls.get());
            assert_eq!(resources, [0]);
            assert_eq!(pass.effects(), &[None, None]);
        }
    }

    #[test]
    fn records_the_live_allocated_resource() {
        let mut trace = TraceLog::default();
        let mut resources = [0u64, 0, 0];
        let mut pass = ActuationPass::new(vec![Some(2)], &mut trace, "test");
        let resource = pass
            .actuate_with(
                0,
                &mut resources,
                |_, _, _| Ok(7),
                |value, prepared| *value = prepared,
                &mut trace,
                "test",
            )
            .unwrap();
        pass.finish(&mut trace, "test").unwrap();
        assert_eq!(resource, 2);
        assert_eq!(resources, [0, 0, 7]);
        assert_eq!(pass.allocation(), pass.effects());
    }

    #[test]
    fn prevents_withdrawal_after_effect_commit() {
        let mut trace = TraceLog::default();
        let mut pass = ActuationPass::new(vec![Some(1)], &mut trace, "test");
        pass.actuate(0, &mut trace, "test").unwrap();
        assert!(pass.deallocate(0, &mut trace, "test").is_err());
    }

    #[test]
    fn rejects_incomplete_closure_and_unallocated_actuation() {
        let mut trace = TraceLog::default();
        let mut pass = ActuationPass::new(vec![Some(0), None], &mut trace, "test");
        assert!(pass.finish(&mut trace, "test").is_err());
        assert!(pass.actuate(1, &mut trace, "test").is_err());
        pass.actuate(0, &mut trace, "test").unwrap();
        pass.finish(&mut trace, "test").unwrap();
        assert!(pass.is_complete());
    }
}
