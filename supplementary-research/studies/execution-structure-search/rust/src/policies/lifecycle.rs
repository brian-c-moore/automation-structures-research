//! Lifecycle policy (docs/execution-modalities.md).
//!
//! Worker spawn/supervise/checkpoint/drain/terminate. Maps to TLA+
//! `LifecyclePolicies.tla`.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LifecyclePolicy {
    Simple,
    Supervision,
    Checkpoint,
    /// Temporal-style continuation-as-new: failure handling spawns a
    /// fresh execution that inherits state, rather than rerunning from
    /// a checkpointed prefix. This is what distinguishes Airflow
    /// (Checkpoint) from Temporal (Continuation).
    Continuation,
    Drain,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WorkerState {
    Unspawned,
    Running,
    Crashed,
    Checkpointed,
    Draining,
    Terminated,
}

#[derive(Debug, Clone)]
pub struct WorkerLifecycle {
    pub state: WorkerState,
    pub policy: LifecyclePolicy,
    pub checkpoints: usize,
    pub max_checkpoints: usize,
    pub restarts: usize,
    pub draining: bool,
}

impl WorkerLifecycle {
    pub fn new(policy: LifecyclePolicy, max_checkpoints: usize) -> Self {
        Self {
            state: WorkerState::Unspawned,
            policy,
            checkpoints: 0,
            max_checkpoints,
            restarts: 0,
            draining: false,
        }
    }

    pub fn spawn(&mut self) -> bool {
        if self.draining || !matches!(self.state, WorkerState::Unspawned) {
            return false;
        }
        self.state = WorkerState::Running;
        true
    }

    pub fn crash(&mut self) -> bool {
        if !matches!(self.state, WorkerState::Running) {
            return false;
        }
        self.state = WorkerState::Crashed;
        true
    }

    /// Supervision policy: restart a crashed worker.
    pub fn supervised_restart(&mut self) -> bool {
        if self.policy != LifecyclePolicy::Supervision {
            return false;
        }
        if !matches!(self.state, WorkerState::Crashed) {
            return false;
        }
        self.state = WorkerState::Running;
        self.restarts += 1;
        true
    }

    /// Checkpoint policy: save a checkpoint.
    pub fn checkpoint(&mut self) -> bool {
        if self.policy != LifecyclePolicy::Checkpoint {
            return false;
        }
        if !matches!(self.state, WorkerState::Running) {
            return false;
        }
        if self.checkpoints >= self.max_checkpoints {
            return false;
        }
        self.checkpoints += 1;
        self.state = WorkerState::Checkpointed;
        true
    }

    /// Restart from a checkpoint.
    pub fn checkpoint_restart(&mut self) -> bool {
        if self.policy != LifecyclePolicy::Checkpoint {
            return false;
        }
        if !matches!(self.state, WorkerState::Checkpointed | WorkerState::Crashed) {
            return false;
        }
        if self.checkpoints == 0 {
            return false;
        }
        self.state = WorkerState::Running;
        self.restarts += 1;
        true
    }

    /// Drain policy: stop accepting new work.
    pub fn start_drain(&mut self) -> bool {
        if self.policy != LifecyclePolicy::Drain || self.draining {
            return false;
        }
        self.draining = true;
        true
    }

    pub fn drain_to_terminate(&mut self) -> bool {
        if self.policy != LifecyclePolicy::Drain || !self.draining {
            return false;
        }
        match self.state {
            WorkerState::Running => {
                self.state = WorkerState::Draining;
                true
            }
            WorkerState::Draining => {
                self.state = WorkerState::Terminated;
                true
            }
            _ => false,
        }
    }

    pub fn terminate_simple(&mut self) -> bool {
        if self.policy != LifecyclePolicy::Simple {
            return false;
        }
        if !matches!(self.state, WorkerState::Running) {
            return false;
        }
        self.state = WorkerState::Terminated;
        true
    }

    /// Invariant: under Simple policy, no restarts ever.
    pub fn check_simple_no_restart(&self) -> bool {
        match self.policy {
            LifecyclePolicy::Simple => self.restarts == 0,
            _ => true,
        }
    }
}
