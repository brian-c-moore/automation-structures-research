//! Supervision and restart: lifecycle policy expressed over actors.
//!
//! Per the execution-modality study: "Supervision and restart are lifecycle concerns:
//! spawn, supervise, restart, terminate."

use crate::actor::mailbox::Pid;
use crate::policies::lifecycle::{LifecyclePolicy, WorkerLifecycle, WorkerState};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RestartStrategy {
    /// One-for-one: only restart the crashed child.
    OneForOne,
    /// One-for-all: any crash restarts every child.
    OneForAll,
}

pub struct Supervisor {
    pub strategy: RestartStrategy,
    pub children: HashMap<Pid, WorkerLifecycle>,
    pub max_restarts_per_child: usize,
}

impl Supervisor {
    pub fn new(strategy: RestartStrategy, max_restarts_per_child: usize) -> Self {
        Self {
            strategy,
            children: HashMap::new(),
            max_restarts_per_child,
        }
    }

    pub fn supervise(&mut self, pid: Pid) {
        self.children
            .insert(pid, WorkerLifecycle::new(LifecyclePolicy::Supervision, 0));
        self.children.get_mut(&pid).unwrap().spawn();
    }

    pub fn child_crashed(&mut self, pid: Pid) {
        if let Some(child) = self.children.get_mut(&pid) {
            child.crash();
        }
        self.respond_to_crash(pid);
    }

    fn respond_to_crash(&mut self, pid: Pid) {
        match self.strategy {
            RestartStrategy::OneForOne => {
                if let Some(child) = self.children.get_mut(&pid) {
                    if child.restarts < self.max_restarts_per_child {
                        child.supervised_restart();
                    }
                }
            }
            RestartStrategy::OneForAll => {
                let pids: Vec<Pid> = self.children.keys().copied().collect();
                for child_pid in pids {
                    let child = self.children.get_mut(&child_pid).unwrap();
                    if matches!(child.state, WorkerState::Running) {
                        child.crash();
                    }
                    if child.restarts < self.max_restarts_per_child {
                        child.supervised_restart();
                    }
                }
            }
        }
    }

    pub fn alive(&self, pid: Pid) -> bool {
        self.children
            .get(&pid)
            .map(|c| matches!(c.state, WorkerState::Running))
            .unwrap_or(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one_for_one_restarts_only_the_crashed_child() {
        let mut sup = Supervisor::new(RestartStrategy::OneForOne, 3);
        sup.supervise(1);
        sup.supervise(2);
        sup.child_crashed(1);
        assert!(sup.alive(1));
        assert!(sup.alive(2));
        assert_eq!(sup.children[&1].restarts, 1);
        assert_eq!(sup.children[&2].restarts, 0);
    }

    #[test]
    fn one_for_all_restarts_every_child() {
        let mut sup = Supervisor::new(RestartStrategy::OneForAll, 3);
        sup.supervise(1);
        sup.supervise(2);
        sup.child_crashed(1);
        assert_eq!(sup.children[&1].restarts, 1);
        assert_eq!(sup.children[&2].restarts, 1);
    }
}
