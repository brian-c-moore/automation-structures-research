//! Workflow-DAG workload (docs/execution-modalities.md).
//!
//! Reproduces Airflow, Dagster, Luigi, Prefect, Temporal. A DAG of
//! named tasks with declared dependencies; some tasks may "fail" in
//! a run, modeled as a `Failure` record emitted by the failing
//! task's operator. The recovery strategy is a workload-internal
//! field whose value (RerunFromFailure for Airflow, ContinuationAsNew
//! for Temporal) determines what kind of recovery event the failing
//! task emits.
//!
//! compatible_modalities = [Sequential, StepGraph], single
//! equivalence class. The dispatcher uses cross-modality output
//! comparison as the equivalence check, so trace_properties is empty.
//!
//! Distinguishability vs. BuildDag: cv.invocation differs at the
//! TOML level (Demand_Pull vs Dependency_Completion); both labels
//! parse to InvocationPolicy::Fifo in the current parse table, so
//! the distinction is policy-label, not enum value. Distinguishability
//! between Airflow and Temporal is at recovery_strategy, observable
//! via the workload's `recovery_events` output.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::modalities::Modality;
use crate::policies::ConfigVector;
use crate::workloads::{Operator, OperatorFactory, Workload};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecoveryStrategy {
    /// Airflow-style: a failed task is rerun from its last checkpoint.
    RerunFromFailure,
    /// Temporal-style: a failed workflow continues as a fresh
    /// execution that inherits state from the prior run.
    ContinuationAsNew,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoveryEvent {
    pub task: String,
    pub strategy: RecoveryStrategy,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WorkflowRecord {
    /// A task completed successfully and produced this result.
    TaskOutput { task: String, result: String },
    /// A task was declared to fail; its operator emitted this record
    /// instead of (or alongside) a TaskOutput.
    TaskFailure { task: String },
    /// The failing task's operator's response under the workload's
    /// configured recovery_strategy.
    Recovery {
        task: String,
        strategy: RecoveryStrategy,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WorkflowDagOutput {
    /// Final result of the target task (None if the target failed
    /// without recovery producing a result).
    pub final_result: Option<String>,
    /// Names of tasks that completed successfully, sorted by task name.
    pub completed_tasks: Vec<String>,
    /// Names of tasks that emitted a TaskFailure record.
    pub failures: Vec<String>,
    /// Recovery events emitted by the failing tasks under the
    /// workload's configured recovery_strategy.
    pub recovery_events: Vec<RecoveryEvent>,
}

#[derive(Debug, Clone)]
pub struct TaskNode {
    pub name: String,
    pub deps: Vec<String>,
    pub transform: fn(Vec<String>) -> String,
}

#[derive(Debug, Clone)]
pub struct WorkflowDagWorkload {
    pub tasks: BTreeMap<String, TaskNode>,
    pub target: String,
    /// Tasks that should emit a TaskFailure record in this run.
    pub failing_tasks: BTreeSet<String>,
    /// Recovery strategy used by failing tasks to emit their
    /// `Recovery` record. Airflow runs construct the workload with
    /// `RerunFromFailure`; Temporal runs with `ContinuationAsNew`.
    pub recovery_strategy: RecoveryStrategy,
}

impl WorkflowDagWorkload {
    pub fn new(
        tasks: BTreeMap<String, TaskNode>,
        target: String,
        failing_tasks: BTreeSet<String>,
        recovery_strategy: RecoveryStrategy,
    ) -> Self {
        Self {
            tasks,
            target,
            failing_tasks,
            recovery_strategy,
        }
    }

    /// Airflow-flavored small example: six tasks with one failure at
    /// `feature` triggering a RerunFromFailure recovery.
    pub fn airflow_example() -> Self {
        Self::small_example_with(RecoveryStrategy::RerunFromFailure)
    }

    /// Temporal-flavored: same task graph and same failing task, but
    /// recovery strategy is ContinuationAsNew.
    pub fn temporal_example() -> Self {
        Self::small_example_with(RecoveryStrategy::ContinuationAsNew)
    }

    pub fn small_example_with(recovery_strategy: RecoveryStrategy) -> Self {
        let mut tasks = BTreeMap::new();
        tasks.insert(
            "ingest".to_string(),
            TaskNode {
                name: "ingest".to_string(),
                deps: vec![],
                transform: |_| "raw".to_string(),
            },
        );
        tasks.insert(
            "clean".to_string(),
            TaskNode {
                name: "clean".to_string(),
                deps: vec!["ingest".to_string()],
                transform: |xs| format!("clean({})", xs.join(",")),
            },
        );
        tasks.insert(
            "feature".to_string(),
            TaskNode {
                name: "feature".to_string(),
                deps: vec!["clean".to_string()],
                transform: |xs| format!("feature({})", xs.join(",")),
            },
        );
        tasks.insert(
            "model_a".to_string(),
            TaskNode {
                name: "model_a".to_string(),
                deps: vec!["feature".to_string()],
                transform: |xs| format!("a({})", xs.join(",")),
            },
        );
        tasks.insert(
            "model_b".to_string(),
            TaskNode {
                name: "model_b".to_string(),
                deps: vec!["feature".to_string()],
                transform: |xs| format!("b({})", xs.join(",")),
            },
        );
        tasks.insert(
            "ensemble".to_string(),
            TaskNode {
                name: "ensemble".to_string(),
                deps: vec!["model_a".to_string(), "model_b".to_string()],
                transform: |xs| format!("ens({})", xs.join(",")),
            },
        );
        let failing: BTreeSet<String> = ["feature".to_string()].into_iter().collect();
        Self::new(tasks, "ensemble".to_string(), failing, recovery_strategy)
    }
}

/// Task operator. Collects records keyed by `task` (predecessor name),
/// applies the declared transform at end-of-stream in declared
/// dependency order, and emits either a TaskOutput record (if the
/// task is not in failing_tasks) or a TaskFailure + Recovery record
/// pair. Even on failure, the operator emits a TaskOutput so that
/// downstream tasks can proceed — the failure marks an observable
/// event in the trace, not a hard abort.
struct TaskOp {
    name: String,
    deps: Vec<String>,
    transform: fn(Vec<String>) -> String,
    is_failing: bool,
    recovery_strategy: RecoveryStrategy,
    collected: HashMap<String, String>,
    observed: Vec<WorkflowRecord>,
}

impl Operator<WorkflowRecord> for TaskOp {
    fn on_record(&mut self, r: WorkflowRecord) -> Vec<WorkflowRecord> {
        if let WorkflowRecord::TaskOutput { task, result } = &r {
            self.collected.insert(task.clone(), result.clone());
        }
        // Preserve upstream trace records so failures, recoveries, and
        // intermediate completions remain observable at a sink. The
        // reduce step deduplicates records replicated by DAG fan-out.
        self.observed.push(r);
        Vec::new()
    }

    fn on_end_of_stream(&mut self) -> Vec<WorkflowRecord> {
        let inputs: Vec<String> = self
            .deps
            .iter()
            .map(|d| {
                self.collected.remove(d).unwrap_or_else(|| {
                    panic!("task `{}` missing predecessor `{}` at EOS", self.name, d)
                })
            })
            .collect();
        let result = (self.transform)(inputs);
        let mut emitted = std::mem::take(&mut self.observed);
        if self.is_failing {
            emitted.push(WorkflowRecord::TaskFailure {
                task: self.name.clone(),
            });
            emitted.push(WorkflowRecord::Recovery {
                task: self.name.clone(),
                strategy: self.recovery_strategy,
            });
        }
        emitted.push(WorkflowRecord::TaskOutput {
            task: self.name.clone(),
            result,
        });
        emitted
    }
}

impl Workload for WorkflowDagWorkload {
    type Record = WorkflowRecord;
    type Output = WorkflowDagOutput;
    type OpId = String;

    fn operators(&self) -> Vec<(String, OperatorFactory<WorkflowRecord>)> {
        let mut out: Vec<(String, OperatorFactory<WorkflowRecord>)> = Vec::new();
        for (name, node) in &self.tasks {
            let name_str = name.clone();
            let deps = node.deps.clone();
            let transform = node.transform;
            let is_failing = self.failing_tasks.contains(name);
            let recovery_strategy = self.recovery_strategy;
            let factory: OperatorFactory<WorkflowRecord> = Box::new(move || {
                Box::new(TaskOp {
                    name: name_str.clone(),
                    deps: deps.clone(),
                    transform,
                    is_failing,
                    recovery_strategy,
                    collected: HashMap::new(),
                    observed: Vec::new(),
                })
            });
            out.push((name.clone(), factory));
        }
        out
    }

    fn edges(&self) -> Vec<(String, String)> {
        let mut e: Vec<(String, String)> = Vec::new();
        for (name, node) in &self.tasks {
            for dep in &node.deps {
                e.push((dep.clone(), name.clone()));
            }
        }
        e
    }

    fn initial_inputs(&self) -> HashMap<String, Vec<WorkflowRecord>> {
        // Source tasks (no deps) have no incoming records; their
        // operator's on_record never fires; on_end_of_stream computes
        // their result from an empty input list (the transform is
        // declared to handle this for sources). Per the Workload
        // trait, every source must appear in initial_inputs, so each is
        // seeded with an empty vector.
        let mut m: HashMap<String, Vec<WorkflowRecord>> = HashMap::new();
        for (name, node) in &self.tasks {
            if node.deps.is_empty() {
                m.insert(name.clone(), Vec::new());
            }
        }
        m
    }

    fn reduce(&self, sink_outputs: HashMap<String, Vec<WorkflowRecord>>) -> WorkflowDagOutput {
        // Order task arrival by sorted task name so two cross-modal
        // runs produce identical Vec ordering. Both Sequential and
        // StepGraph traverse operators in topological order then break
        // ties on OpId — the resulting completed_tasks/failures/
        // recovery_events vectors are the deterministic projection.
        let mut by_task: BTreeMap<String, Vec<WorkflowRecord>> = BTreeMap::new();
        for (id, recs) in sink_outputs {
            by_task.entry(id).or_default().extend(recs);
        }

        let mut completed: Vec<String> = Vec::new();
        let mut failures: Vec<String> = Vec::new();
        let mut recovery_events: Vec<RecoveryEvent> = Vec::new();
        let mut final_result: Option<String> = None;
        for (id, recs) in &by_task {
            for r in recs {
                match r {
                    WorkflowRecord::TaskOutput { task, result } => {
                        if !completed.contains(task) {
                            completed.push(task.clone());
                        }
                        if id == &self.target {
                            final_result = Some(result.clone());
                        }
                    }
                    WorkflowRecord::TaskFailure { task } => {
                        if !failures.contains(task) {
                            failures.push(task.clone());
                        }
                    }
                    WorkflowRecord::Recovery { task, strategy } => {
                        let event = RecoveryEvent {
                            task: task.clone(),
                            strategy: *strategy,
                        };
                        if !recovery_events.contains(&event) {
                            recovery_events.push(event);
                        }
                    }
                }
            }
        }
        completed.sort();
        failures.sort();
        recovery_events.sort_by(|left, right| left.task.cmp(&right.task));
        WorkflowDagOutput {
            final_result,
            completed_tasks: completed,
            failures,
            recovery_events,
        }
    }

    fn compatible_modalities(&self) -> &'static [Modality] {
        &[Modality::Sequential, Modality::StepGraph]
    }

    fn equivalence_classes(&self) -> Vec<Vec<Modality>> {
        vec![vec![Modality::Sequential, Modality::StepGraph]]
    }

    fn trace_properties(&self, _cv: &ConfigVector) -> Vec<Box<dyn Fn(&WorkflowDagOutput) -> bool>> {
        // Cross-modality output comparison is the verification path here,
        // so no additional trace properties are needed.
        Vec::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modalities::{run_sequential, run_step_graph};
    use crate::policies::ConfigVector;

    #[test]
    fn airflow_example_reaches_ensemble_with_one_failure_recorded() {
        let w = WorkflowDagWorkload::airflow_example();
        let cv = ConfigVector::default();
        let out = run_sequential(&w, &cv);
        assert_eq!(
            out.final_result.as_deref(),
            Some("ens(a(feature(clean(raw))),b(feature(clean(raw))))")
        );
        assert_eq!(out.failures, vec!["feature".to_string()]);
        let completed: BTreeSet<String> = out.completed_tasks.into_iter().collect();
        assert_eq!(completed, w.tasks.keys().cloned().collect());
        assert_eq!(out.recovery_events.len(), 1);
        assert_eq!(out.recovery_events[0].task, "feature");
        assert_eq!(
            out.recovery_events[0].strategy,
            RecoveryStrategy::RerunFromFailure
        );
    }

    #[test]
    fn step_graph_matches_sequential_on_airflow_example() {
        let w = WorkflowDagWorkload::airflow_example();
        let cv = ConfigVector::default();
        let seq = run_sequential(&w, &cv);
        let step = run_step_graph(&w, &cv).expect("acyclic");
        assert_eq!(seq, step);
    }
}
