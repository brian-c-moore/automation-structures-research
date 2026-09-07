use crate::{Structure, StructureError, TraceLog};
use automation_structures::Sequential as PublishedSequential;

/// Typed-payload trace adapter over the published `Sequential` transition owner.
pub struct Sequential<T> {
    inner: PublishedSequential,
    value: T,
    history: Vec<T>,
}

impl<T: Clone> Sequential<T> {
    pub fn new(
        planned_steps: u64,
        initial_value: T,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<Self, StructureError> {
        let steps = usize::try_from(planned_steps)
            .map_err(|_| StructureError::new("sequential step count does not fit usize"))?;
        let value_domain_size = planned_steps
            .checked_add(1)
            .ok_or_else(|| StructureError::new("sequential ordinal domain overflow"))?;
        let inner = PublishedSequential::new(steps, value_domain_size, 0).map_err(|error| {
            StructureError::new(format!(
                "published Sequential rejected construction: {error}"
            ))
        })?;
        trace.emit(
            Structure::Sequential,
            "Initialize",
            subject,
            format!("planned_steps={planned_steps}"),
        );
        Ok(Self {
            inner,
            value: initial_value,
            history: Vec::new(),
        })
    }

    pub fn pc(&self) -> u64 {
        self.inner.completed() as u64
    }

    pub fn value(&self) -> &T {
        &self.value
    }

    pub fn history(&self) -> &[T] {
        &self.history
    }

    pub fn begin_step(
        &mut self,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<u64, StructureError> {
        let step = self.pc();
        if !self.inner.begin_step() {
            return Err(StructureError::new(
                "published Sequential rejected BeginStep",
            ));
        }
        trace.emit(
            Structure::Sequential,
            "Begin",
            subject,
            format!("step={step}"),
        );
        Ok(step)
    }

    pub fn complete_step(
        &mut self,
        step: u64,
        next_value: T,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<(), StructureError> {
        if step != self.pc() {
            return Err(StructureError::new(format!(
                "sequential completion {step} does not match active step {}",
                self.pc()
            )));
        }
        let next_ordinal = step
            .checked_add(1)
            .ok_or_else(|| StructureError::new("sequential ordinal overflow"))?;
        if !self.inner.complete_step(next_ordinal) {
            return Err(StructureError::new(
                "published Sequential rejected CompleteStep",
            ));
        }
        self.value = next_value.clone();
        self.history.push(next_value);
        trace.emit(
            Structure::Sequential,
            "Complete",
            subject,
            format!("step={step} completed={}", self.pc()),
        );
        Ok(())
    }

    pub fn done_stuttering(
        &self,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<(), StructureError> {
        if !self.inner.is_done() {
            return Err(StructureError::new(
                "published Sequential is not at its terminal inactive state",
            ));
        }
        trace.emit(
            Structure::Sequential,
            "Done",
            subject,
            format!("completed={}", self.pc()),
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn history_tracks_completed_steps() {
        let mut trace = TraceLog::default();
        let mut carrier = Sequential::new(2, 0u64, &mut trace, "test").unwrap();
        let first = carrier.begin_step(&mut trace, "step-0").unwrap();
        carrier
            .complete_step(first, 7, &mut trace, "step-0")
            .unwrap();
        let second = carrier.begin_step(&mut trace, "step-1").unwrap();
        carrier
            .complete_step(second, 9, &mut trace, "step-1")
            .unwrap();
        carrier.done_stuttering(&mut trace, "test").unwrap();
        assert_eq!(carrier.pc(), 2);
        assert_eq!(carrier.value(), &9);
        assert_eq!(carrier.history(), &[7, 9]);
    }

    #[test]
    fn rejects_overlap_and_nonterminal_done() {
        let mut trace = TraceLog::default();
        let mut carrier = Sequential::new(1, 0u64, &mut trace, "test").unwrap();
        let step = carrier.begin_step(&mut trace, "step-0").unwrap();
        assert!(carrier.begin_step(&mut trace, "step-0").is_err());
        assert!(carrier.done_stuttering(&mut trace, "test").is_err());
        carrier
            .complete_step(step, 1, &mut trace, "step-0")
            .unwrap();
        carrier.done_stuttering(&mut trace, "test").unwrap();
    }

    #[test]
    fn rejects_an_empty_plan() {
        let mut trace = TraceLog::default();
        assert!(Sequential::new(0, 0u64, &mut trace, "test").is_err());
    }
}
