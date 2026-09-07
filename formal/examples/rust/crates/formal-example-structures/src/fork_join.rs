use crate::{Structure, StructureError, TraceLog};
use automation_structures::{
    ForkJoin as PublishedForkJoin, ForkJoinPhase as PublishedPhase,
    WorkerState as PublishedWorkerState,
};

/// Trace adapter over the published finite-index `ForkJoin` carrier.
pub struct ForkJoin {
    inner: PublishedForkJoin,
    value_domain_size: u64,
    initial_value: u64,
}

impl ForkJoin {
    pub fn new(
        workers: usize,
        value_domain_size: u64,
        initial_value: u64,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<Self, StructureError> {
        let inner =
            PublishedForkJoin::new(workers, value_domain_size, initial_value).map_err(|error| {
                StructureError::new(format!("published ForkJoin rejected construction: {error}"))
            })?;
        trace.emit(
            Structure::ForkJoin,
            "Initialize",
            subject,
            format!("workers={workers} value_domain_size={value_domain_size}"),
        );
        Ok(Self {
            inner,
            value_domain_size,
            initial_value,
        })
    }

    pub fn worker_states(&self) -> Vec<u8> {
        self.inner
            .worker_states()
            .iter()
            .map(|state| match state {
                PublishedWorkerState::Ready => 0,
                PublishedWorkerState::Running => 1,
                PublishedWorkerState::Complete => 2,
            })
            .collect()
    }

    pub fn worker_values(&self) -> &[u64] {
        self.inner.worker_values()
    }

    pub fn phase(&self) -> u8 {
        match self.inner.phase() {
            PublishedPhase::Fork => 0,
            PublishedPhase::Join => 1,
            PublishedPhase::Done => 2,
        }
    }

    pub fn output_ready(&self) -> bool {
        self.inner.output_ready()
    }

    pub fn output_snapshot(&self) -> &[u64] {
        self.inner.outputs().unwrap_or(&[])
    }

    pub fn all_complete(&self) -> bool {
        self.inner
            .worker_states()
            .iter()
            .all(|state| *state == PublishedWorkerState::Complete)
    }

    pub fn start_worker(
        &mut self,
        worker: usize,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<(), StructureError> {
        if !self.inner.start_worker(worker) {
            return Err(StructureError::new(format!(
                "published ForkJoin rejected StartWorker for {worker}"
            )));
        }
        trace.emit(
            Structure::ForkJoin,
            "StartWorker",
            subject,
            format!("worker={worker}"),
        );
        Ok(())
    }

    pub fn complete_worker(
        &mut self,
        worker: usize,
        value: u64,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<(), StructureError> {
        if !self.inner.complete_worker(worker, value) {
            return Err(StructureError::new(format!(
                "published ForkJoin rejected CompleteWorker for {worker} with value {value}"
            )));
        }
        trace.emit(
            Structure::ForkJoin,
            "CompleteWorker",
            subject,
            format!("worker={worker} value={value}"),
        );
        Ok(())
    }

    pub fn barrier(&mut self, trace: &mut TraceLog, subject: &str) -> Result<(), StructureError> {
        if !self.inner.barrier() {
            return Err(StructureError::new(
                "published ForkJoin rejected the barrier",
            ));
        }
        trace.emit(
            Structure::ForkJoin,
            "Barrier",
            subject,
            format!("workers={}", self.inner.len()),
        );
        Ok(())
    }

    pub fn produce_output(
        &mut self,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<(), StructureError> {
        if !self.inner.produce_output() {
            return Err(StructureError::new(
                "published ForkJoin rejected output publication",
            ));
        }
        trace.emit(
            Structure::ForkJoin,
            "ProduceOutput",
            subject,
            format!("values={:?}", self.output_snapshot()),
        );
        Ok(())
    }

    pub fn done_stuttering(
        &self,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<(), StructureError> {
        if self.inner.phase() != PublishedPhase::Done || !self.inner.output_ready() {
            return Err(StructureError::new(
                "published ForkJoin is not at its terminal output state",
            ));
        }
        trace.emit(
            Structure::ForkJoin,
            "Done",
            subject,
            format!("workers={}", self.inner.len()),
        );
        Ok(())
    }
}

impl Clone for ForkJoin {
    fn clone(&self) -> Self {
        let mut inner =
            PublishedForkJoin::new(self.inner.len(), self.value_domain_size, self.initial_value)
                .expect("published ForkJoin configuration must replay");
        for worker in 0..self.inner.len() {
            match self.inner.worker_state(worker) {
                Some(PublishedWorkerState::Ready) => {}
                Some(PublishedWorkerState::Running) => {
                    assert!(inner.start_worker(worker));
                }
                Some(PublishedWorkerState::Complete) => {
                    assert!(inner.start_worker(worker));
                    let value = self
                        .inner
                        .worker_value(worker)
                        .expect("published complete worker has a value");
                    assert!(inner.complete_worker(worker, value));
                }
                None => unreachable!("worker ordinal is bounded by len"),
            }
        }
        if self.inner.phase() != PublishedPhase::Fork {
            assert!(inner.barrier());
        }
        if self.inner.phase() == PublishedPhase::Done {
            assert!(inner.produce_output());
        }
        Self {
            inner,
            value_domain_size: self.value_domain_size,
            initial_value: self.initial_value,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_three_worker_barrier_publishes_exact_snapshot() {
        let mut trace = TraceLog::default();
        let mut fork = ForkJoin::new(3, 10, 0, &mut trace, "fork").unwrap();
        assert!(fork.produce_output(&mut trace, "fork").is_err());
        assert!(fork.barrier(&mut trace, "fork").is_err());
        fork.start_worker(0, &mut trace, "worker-0").unwrap();
        fork.start_worker(1, &mut trace, "worker-1").unwrap();
        fork.complete_worker(0, 4, &mut trace, "worker-0").unwrap();
        assert!(fork.barrier(&mut trace, "fork").is_err());
        fork.start_worker(2, &mut trace, "worker-2").unwrap();
        fork.complete_worker(2, 8, &mut trace, "worker-2").unwrap();
        fork.complete_worker(1, 6, &mut trace, "worker-1").unwrap();
        fork.barrier(&mut trace, "fork").unwrap();
        fork.produce_output(&mut trace, "fork").unwrap();
        fork.done_stuttering(&mut trace, "fork").unwrap();
        assert_eq!(fork.worker_values(), &[4, 6, 8]);
        assert_eq!(fork.output_snapshot(), &[4, 6, 8]);
        assert!(fork.output_ready());
        assert_eq!(fork.phase(), 2);
    }

    #[test]
    fn worker_cannot_complete_before_start_or_after_barrier() {
        let mut trace = TraceLog::default();
        let mut fork = ForkJoin::new(1, 2, 0, &mut trace, "fork").unwrap();
        assert!(fork.complete_worker(0, 1, &mut trace, "worker-0").is_err());
        fork.start_worker(0, &mut trace, "worker-0").unwrap();
        fork.complete_worker(0, 1, &mut trace, "worker-0").unwrap();
        fork.barrier(&mut trace, "fork").unwrap();
        assert!(fork.start_worker(0, &mut trace, "worker-0").is_err());
    }
}
