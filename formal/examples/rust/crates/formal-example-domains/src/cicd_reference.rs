use serde::Serialize;
use std::collections::BTreeSet;

/// Six valid worker start/complete interleavings times the 45 ways to place the
/// two-event static-analysis chain among the eight events of the test chain.
pub const EXPECTED_SCHEDULE_COUNT: usize = 6 * 45;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum PipelineEvent {
    StartJob(usize),
    CompleteJob(usize),
    StartWorker(usize),
    CompleteWorker(usize),
    Barrier,
    PublishTestOutput,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ReferenceState {
    job_state: [u8; 4],
    worker_state: [u8; 2],
    barrier_crossed: bool,
    output_published: bool,
}

impl ReferenceState {
    fn initial() -> Self {
        Self {
            job_state: [0; 4],
            worker_state: [0; 2],
            barrier_crossed: false,
            output_published: false,
        }
    }

    fn terminal(&self) -> bool {
        self.job_state == [2; 4]
            && self.worker_state == [2; 2]
            && self.barrier_crossed
            && self.output_published
    }

    fn predecessors_complete(&self, job: usize) -> bool {
        match job {
            0 => true,
            1 | 2 => self.job_state[0] == 2,
            3 => self.job_state[1] == 2 && self.job_state[2] == 2,
            _ => false,
        }
    }

    fn enabled(&self) -> Vec<PipelineEvent> {
        let mut events = Vec::new();
        for job in 0..4 {
            if self.job_state[job] == 0 && self.predecessors_complete(job) {
                events.push(PipelineEvent::StartJob(job));
            }
            if self.job_state[job] == 1 && (job != 2 || self.output_published) {
                events.push(PipelineEvent::CompleteJob(job));
            }
        }
        if self.job_state[2] == 1 && !self.barrier_crossed {
            for worker in 0..2 {
                match self.worker_state[worker] {
                    0 => events.push(PipelineEvent::StartWorker(worker)),
                    1 => events.push(PipelineEvent::CompleteWorker(worker)),
                    _ => {}
                }
            }
            if self.worker_state == [2; 2] {
                events.push(PipelineEvent::Barrier);
            }
        }
        if self.barrier_crossed && !self.output_published {
            events.push(PipelineEvent::PublishTestOutput);
        }
        events
    }

    fn apply(&mut self, event: PipelineEvent) {
        match event {
            PipelineEvent::StartJob(job) => self.job_state[job] = 1,
            PipelineEvent::CompleteJob(job) => self.job_state[job] = 2,
            PipelineEvent::StartWorker(worker) => self.worker_state[worker] = 1,
            PipelineEvent::CompleteWorker(worker) => self.worker_state[worker] = 2,
            PipelineEvent::Barrier => self.barrier_crossed = true,
            PipelineEvent::PublishTestOutput => self.output_published = true,
        }
    }
}

fn enumerate_from(
    state: ReferenceState,
    prefix: &mut Vec<PipelineEvent>,
    schedules: &mut Vec<Vec<PipelineEvent>>,
) {
    if state.terminal() {
        schedules.push(prefix.clone());
        return;
    }
    for event in state.enabled() {
        let mut next = state.clone();
        next.apply(event);
        prefix.push(event);
        enumerate_from(next, prefix, schedules);
        prefix.pop();
    }
}

/// Enumerate every event ordering admitted by a plain-state interpretation of
/// the frozen pipeline. This module does not call a catalog structure or the
/// executable construction.
pub fn enumerate_schedules() -> Vec<Vec<PipelineEvent>> {
    let mut schedules = Vec::new();
    enumerate_from(ReferenceState::initial(), &mut Vec::new(), &mut schedules);
    schedules.sort();
    schedules.dedup();
    schedules
}

pub fn enumerate_dependency_schedules() -> Vec<Vec<PipelineEvent>> {
    enumerate_schedules()
}

pub fn enumerate_partition_schedules() -> Vec<Vec<PipelineEvent>> {
    enumerate_schedules()
}

pub fn expected_outputs() -> BTreeSet<String> {
    [
        "compile",
        "static-analysis",
        "test-linux",
        "test-windows",
        "test-matrix",
        "package",
    ]
    .into_iter()
    .map(str::to_string)
    .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enumerator_produces_only_complete_unique_schedules() {
        let schedules = enumerate_schedules();
        assert_eq!(schedules.len(), EXPECTED_SCHEDULE_COUNT);
        let unique: BTreeSet<_> = schedules.iter().collect();
        assert_eq!(unique.len(), schedules.len());
        assert!(schedules.iter().all(|schedule| schedule.len() == 14));
    }
}
