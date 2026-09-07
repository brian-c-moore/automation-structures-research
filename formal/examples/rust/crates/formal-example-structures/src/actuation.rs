use crate::{Structure, StructureError, TraceLog};
use automation_structures::ActuationPass as PublishedActuationPass;

/// Trace adapter over the published `ActuationPass` implementation.
///
/// Transition admission and carrier state are owned by
/// `crate://automation-structures/0.2.3/src/primitives/actuation_pass.rs`.
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

    pub fn actuate_with<T>(
        &mut self,
        seat: usize,
        resources: &mut [T],
        operation: impl FnOnce(&mut T, &mut TraceLog, &str) -> Result<(), StructureError>,
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
        operation(target, trace, subject)?;
        self.inner
            .actuate(seat)
            .map_err(|error| structure_error("actuate", error))?;
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
            format!("effects={}", self.inner.effects().iter().flatten().count()),
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
    fn records_the_live_allocated_resource() {
        let mut trace = TraceLog::default();
        let mut resources = [0u64, 0, 0];
        let mut pass = ActuationPass::new(vec![Some(2)], &mut trace, "test");
        let resource = pass
            .actuate_with(
                0,
                &mut resources,
                |value, _, _| {
                    *value = 7;
                    Ok(())
                },
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
