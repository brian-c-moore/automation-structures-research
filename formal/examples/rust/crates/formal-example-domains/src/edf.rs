use formal_example_structures::{
    ActuationPass, Budget, CompetitiveSelection, RecipeEdge, ResourceRegistry, SelectThenActuate,
    SelectionActuationOutcome, Sequential, Structure, StructureError, TraceLog, Unit,
};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

const ADMISSION_SUBJECT: &str = "FEX-DOM-RT-01::admission";
const EXECUTION_SUBJECT: &str = "FEX-DOM-RT-01::execution";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExecutionTicks;

impl Unit for ExecutionTicks {
    const NAME: &'static str = "ExecutionTicks";
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct TaskSpec {
    pub id: String,
    pub wcet: u64,
    pub relative_deadline: u64,
    pub period: u64,
}

impl TaskSpec {
    pub fn new(id: &str, wcet: u64, relative_deadline: u64, period: u64) -> Self {
        Self {
            id: id.to_string(),
            wcet,
            relative_deadline,
            period,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct ReleaseEvent {
    pub time: u64,
    pub task_id: String,
}

impl ReleaseEvent {
    pub fn new(time: u64, task_id: &str) -> Self {
        Self {
            time,
            task_id: task_id.to_string(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum EdfControl {
    None,
    BypassAdmissionCharges,
    UtilizationOnly,
    ReverseUrgency,
    SuppressProgress,
    AccelerateProgress,
    MisdirectActuation,
    OmitReadyCandidate,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct AdmissionCertificate {
    pub hyperperiod: u64,
    pub feasibility_bound: u64,
    pub checked_intervals: u64,
    pub repeating_demand: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct AdmissionDecision {
    pub admitted: bool,
    pub certificate: Option<AdmissionCertificate>,
    pub rejection: Option<String>,
    registry: Option<ResourceRegistry<TaskSpec>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DispatchRecord {
    pub time: u64,
    pub task_id: String,
    pub job_sequence: u64,
    pub absolute_deadline: u64,
    pub completed: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DeadlineMiss {
    pub time: u64,
    pub task_id: String,
    pub job_sequence: u64,
    pub absolute_deadline: u64,
    pub remaining: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ScheduleResult {
    pub horizon: u64,
    pub dispatches: Vec<DispatchRecord>,
    pub misses: Vec<DeadlineMiss>,
    pub completed_jobs: usize,
    quantum_witnesses: Vec<QuantumWitness>,
    job_accounting: Vec<JobAccounting>,
    sequential_history: Vec<Option<usize>>,
}

impl ScheduleResult {
    pub fn no_deadline_miss(&self) -> bool {
        self.misses.is_empty()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct EdfRun {
    pub admission: AdmissionDecision,
    pub schedule: Option<ScheduleResult>,
    pub trace: TraceLog,
}

#[derive(Clone, Debug)]
struct JobState {
    task_id: String,
    sequence: u64,
    release: u64,
    absolute_deadline: u64,
    execution_budget: Budget<ExecutionTicks>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
struct QuantumWitness {
    time: u64,
    subject: String,
    outcome: Option<SelectionActuationOutcome>,
    resource: usize,
    charged: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
struct JobAccounting {
    task_id: String,
    sequence: u64,
    release: u64,
    absolute_deadline: u64,
    declared: u64,
    spent: u64,
    dispatches: u64,
}

pub const EXECUTION_STRUCTURES: [Structure; 4] = [
    Structure::Sequential,
    Structure::CompetitiveSelection,
    Structure::Budget,
    Structure::ActuationPass,
];

pub const EXECUTION_EDGES: [RecipeEdge; 4] = [
    RecipeEdge {
        before: Structure::Sequential,
        before_action: "Begin",
        after: Structure::CompetitiveSelection,
        after_action: "Evaluate",
    },
    RecipeEdge {
        before: Structure::CompetitiveSelection,
        before_action: "Commit",
        after: Structure::Budget,
        after_action: "Check",
    },
    RecipeEdge {
        before: Structure::Budget,
        before_action: "Commit",
        after: Structure::ActuationPass,
        after_action: "Commit",
    },
    RecipeEdge {
        before: Structure::ActuationPass,
        before_action: "Commit",
        after: Structure::Sequential,
        after_action: "Complete",
    },
];

fn quantum_subject(time: u64) -> String {
    format!("{EXECUTION_SUBJECT}::quantum::{time}")
}

fn repeating_admission_subject() -> String {
    format!("{ADMISSION_SUBJECT}::repeating")
}

fn interval_admission_subject(interval: u64) -> String {
    format!("{ADMISSION_SUBJECT}::interval::{interval}")
}

fn job_subject(task_id: &str, sequence: u64) -> String {
    format!("{EXECUTION_SUBJECT}::job::{task_id}::{sequence}")
}

fn gcd(mut left: u64, mut right: u64) -> u64 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left
}

fn checked_lcm(left: u64, right: u64) -> Result<u64, StructureError> {
    left.checked_div(gcd(left, right))
        .and_then(|value| value.checked_mul(right))
        .ok_or_else(|| StructureError::new("task periods overflow the feasibility interval"))
}

fn validate_tasks(tasks: &[TaskSpec]) -> Result<(), StructureError> {
    if tasks.is_empty() {
        return Err(StructureError::new(
            "EDF admission requires at least one task",
        ));
    }
    let mut ids = BTreeSet::new();
    for task in tasks {
        if task.id.is_empty() {
            return Err(StructureError::new("EDF task identity cannot be empty"));
        }
        if !ids.insert(task.id.as_str()) {
            return Err(StructureError::new(format!(
                "EDF task identity {} is duplicated",
                task.id
            )));
        }
        if task.wcet == 0 || task.relative_deadline == 0 || task.period == 0 {
            return Err(StructureError::new(format!(
                "EDF task {} requires positive WCET, deadline, and period",
                task.id
            )));
        }
    }
    Ok(())
}

fn hyperperiod(tasks: &[TaskSpec]) -> Result<u64, StructureError> {
    tasks
        .iter()
        .try_fold(1, |current, task| checked_lcm(current, task.period))
}

fn interval_demand(task: &TaskSpec, interval: u64) -> Result<u64, StructureError> {
    if interval < task.relative_deadline {
        return Ok(0);
    }
    let jobs = (interval - task.relative_deadline)
        .checked_div(task.period)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| StructureError::new("interval demand job count overflow"))?;
    jobs.checked_mul(task.wcet)
        .ok_or_else(|| StructureError::new("interval demand charge overflow"))
}

pub fn admit_task_set(
    tasks: &[TaskSpec],
    trace: &mut TraceLog,
    control: EdfControl,
) -> Result<AdmissionDecision, StructureError> {
    validate_tasks(tasks)?;
    let common_period = hyperperiod(tasks)?;
    let max_deadline = tasks
        .iter()
        .map(|task| task.relative_deadline)
        .max()
        .ok_or_else(|| StructureError::new("EDF admission has no deadline"))?;
    let feasibility_bound = common_period
        .checked_add(max_deadline)
        .ok_or_else(|| StructureError::new("EDF feasibility bound overflow"))?;

    let mut repeating_demand = 0u64;
    for task in tasks {
        let releases = common_period / task.period;
        let charge = releases
            .checked_mul(task.wcet)
            .ok_or_else(|| StructureError::new("EDF repeating demand overflow"))?;
        repeating_demand = repeating_demand
            .checked_add(charge)
            .ok_or_else(|| StructureError::new("EDF total repeating demand overflow"))?;
    }
    if control != EdfControl::BypassAdmissionCharges {
        let subject = repeating_admission_subject();
        let mut repeating_budget = Budget::<ExecutionTicks>::new(common_period, trace, &subject);
        if let Err(error) = repeating_budget.try_reserve(repeating_demand, trace, &subject) {
            return Ok(AdmissionDecision {
                admitted: false,
                certificate: None,
                rejection: Some(error.to_string()),
                registry: None,
            });
        }
    }

    let mut checked_intervals = 0;
    if control != EdfControl::UtilizationOnly && control != EdfControl::BypassAdmissionCharges {
        for interval in 1..=feasibility_bound {
            let mut total_demand = 0u64;
            for task in tasks {
                let charge = interval_demand(task, interval)?;
                total_demand = total_demand
                    .checked_add(charge)
                    .ok_or_else(|| StructureError::new("EDF interval demand overflow"))?;
            }
            let subject = interval_admission_subject(interval);
            let mut interval_budget = Budget::<ExecutionTicks>::new(interval, trace, &subject);
            if let Err(error) = interval_budget.try_reserve(total_demand, trace, &subject) {
                return Ok(AdmissionDecision {
                    admitted: false,
                    certificate: None,
                    rejection: Some(format!("interval={interval}: {error}")),
                    registry: None,
                });
            }
            checked_intervals += 1;
        }
    }

    let registry = ResourceRegistry::build(
        tasks.iter().cloned().map(|task| (task.id.clone(), task)),
        trace,
        ADMISSION_SUBJECT,
    )?;

    Ok(AdmissionDecision {
        admitted: true,
        certificate: Some(AdmissionCertificate {
            hyperperiod: common_period,
            feasibility_bound,
            checked_intervals,
            repeating_demand,
        }),
        rejection: None,
        registry: Some(registry),
    })
}

fn record_misses(jobs: &[JobState], time: u64, misses: &mut Vec<DeadlineMiss>) {
    for job in jobs {
        if job.execution_budget.remaining() > 0
            && job.absolute_deadline <= time
            && !misses
                .iter()
                .any(|miss| miss.task_id == job.task_id && miss.job_sequence == job.sequence)
        {
            misses.push(DeadlineMiss {
                time,
                task_id: job.task_id.clone(),
                job_sequence: job.sequence,
                absolute_deadline: job.absolute_deadline,
                remaining: job.execution_budget.remaining(),
            });
        }
    }
}

fn validate_release_trace(
    tasks: &[TaskSpec],
    releases: &[ReleaseEvent],
    horizon: u64,
) -> Result<(), StructureError> {
    let task_by_id: BTreeMap<_, _> = tasks.iter().map(|task| (task.id.as_str(), task)).collect();
    let mut previous_time = None;
    let mut last_by_task = BTreeMap::<&str, u64>::new();
    for release in releases {
        if release.time >= horizon {
            return Err(StructureError::new(format!(
                "release for {} at {} lies outside horizon {horizon}",
                release.task_id, release.time
            )));
        }
        if previous_time
            .map(|previous| release.time < previous)
            .unwrap_or(false)
        {
            return Err(StructureError::new(
                "release trace must be ordered by nondecreasing time",
            ));
        }
        previous_time = Some(release.time);
        let task = task_by_id.get(release.task_id.as_str()).ok_or_else(|| {
            StructureError::new(format!(
                "release trace references unknown task {}",
                release.task_id
            ))
        })?;
        if let Some(previous) = last_by_task.insert(task.id.as_str(), release.time) {
            let separation = release.time - previous;
            if separation < task.period {
                return Err(StructureError::new(format!(
                    "task {} released after {separation} ticks but requires {}",
                    task.id, task.period
                )));
            }
        }
    }
    Ok(())
}

fn periodic_release_trace(
    tasks: &[TaskSpec],
    horizon: u64,
) -> Result<Vec<ReleaseEvent>, StructureError> {
    let mut releases = Vec::new();
    for task in tasks {
        let mut time = 0u64;
        while time < horizon {
            let deadline = time
                .checked_add(task.relative_deadline)
                .ok_or_else(|| StructureError::new("periodic deadline overflow"))?;
            if deadline <= horizon {
                releases.push(ReleaseEvent::new(time, &task.id));
            }
            time = time
                .checked_add(task.period)
                .ok_or_else(|| StructureError::new("periodic release time overflow"))?;
        }
    }
    releases.sort();
    Ok(releases)
}

fn execute_release_trace(
    tasks: &[TaskSpec],
    releases: &[ReleaseEvent],
    horizon: u64,
    trace: &mut TraceLog,
    control: EdfControl,
) -> Result<ScheduleResult, StructureError> {
    validate_tasks(tasks)?;
    validate_release_trace(tasks, releases, horizon)?;
    let task_index_by_id: BTreeMap<_, _> = tasks
        .iter()
        .enumerate()
        .map(|(index, task)| (task.id.as_str(), index))
        .collect();
    let mut jobs = Vec::<JobState>::new();
    let mut next_sequence = vec![0u64; tasks.len()];
    let mut release_cursor = 0usize;
    let mut dispatches = Vec::new();
    let mut misses = Vec::new();
    let mut quantum_witnesses = Vec::new();
    let mut sequential = Sequential::new(horizon, None::<usize>, trace, EXECUTION_SUBJECT)?;

    for time in 0..horizon {
        record_misses(&jobs, time, &mut misses);
        while release_cursor < releases.len() && releases[release_cursor].time == time {
            let release = &releases[release_cursor];
            let task_index = *task_index_by_id
                .get(release.task_id.as_str())
                .ok_or_else(|| StructureError::new("validated release lost its task identity"))?;
            let task = &tasks[task_index];
            let sequence = next_sequence[task_index];
            next_sequence[task_index] = sequence
                .checked_add(1)
                .ok_or_else(|| StructureError::new("EDF job sequence overflow"))?;
            let absolute_deadline = time
                .checked_add(task.relative_deadline)
                .ok_or_else(|| StructureError::new("EDF absolute deadline overflow"))?;
            jobs.push(JobState {
                task_id: task.id.clone(),
                sequence,
                release: time,
                absolute_deadline,
                execution_budget: Budget::<ExecutionTicks>::new(
                    task.wcet,
                    trace,
                    &job_subject(&task.id, sequence),
                ),
            });
            release_cursor += 1;
        }

        let subject = quantum_subject(time);
        let step = sequential.begin_step(trace, &subject)?;
        let mut ready: Vec<usize> = jobs
            .iter()
            .enumerate()
            .filter(|(_, job)| job.release <= time && job.execution_budget.remaining() > 0)
            .map(|(index, _)| index)
            .collect();
        if control == EdfControl::OmitReadyCandidate && ready.len() > 1 {
            ready.remove(0);
        }

        if !ready.is_empty() {
            let spent_before: Vec<u64> = jobs
                .iter()
                .map(|job| job.execution_budget.spent())
                .collect();
            let charge_amount = if control == EdfControl::SuppressProgress {
                0
            } else if control == EdfControl::AccelerateProgress {
                2
            } else {
                1
            };
            let urgency_key = |job: &JobState| {
                let deadline_key = if control == EdfControl::ReverseUrgency {
                    u64::MAX - job.absolute_deadline
                } else {
                    job.absolute_deadline
                };
                (deadline_key, job.release, job.task_id.clone(), job.sequence)
            };

            let outcome = if control == EdfControl::MisdirectActuation {
                let selected_position = CompetitiveSelection::select_min_index(
                    &ready,
                    |job_index| urgency_key(&jobs[*job_index]),
                    trace,
                    &subject,
                )?;
                let wrong_position = if ready.len() > 1 {
                    (selected_position + 1) % ready.len()
                } else {
                    selected_position
                };
                let wrong_resource = ready[wrong_position];
                let mut actuation = ActuationPass::new(vec![Some(wrong_resource)], trace, &subject);
                actuation.actuate_with(
                    0,
                    &mut jobs,
                    |job, trace, subject| {
                        if charge_amount == 0 {
                            Ok(())
                        } else {
                            job.execution_budget
                                .try_reserve(charge_amount, trace, subject)
                        }
                    },
                    trace,
                    &subject,
                )?;
                actuation.finish(trace, &subject)?;
                None
            } else {
                Some(SelectThenActuate::select_min_and_actuate(
                    &mut jobs,
                    &ready,
                    urgency_key,
                    |job, trace, subject| {
                        if charge_amount == 0 {
                            Ok(())
                        } else {
                            job.execution_budget
                                .try_reserve(charge_amount, trace, subject)
                        }
                    },
                    trace,
                    &subject,
                )?)
            };
            let selected_index = outcome
                .as_ref()
                .map(SelectionActuationOutcome::resource)
                .unwrap_or_else(|| {
                    jobs.iter()
                        .enumerate()
                        .find(|(index, job)| job.execution_budget.spent() != spent_before[*index])
                        .map(|(index, _)| index)
                        .unwrap_or(ready[0])
                });
            let charged = jobs[selected_index]
                .execution_budget
                .spent()
                .checked_sub(spent_before[selected_index])
                .ok_or_else(|| StructureError::new("execution accounting regressed"))?;
            let job = &jobs[selected_index];
            dispatches.push(DispatchRecord {
                time,
                task_id: job.task_id.clone(),
                job_sequence: job.sequence,
                absolute_deadline: job.absolute_deadline,
                completed: job.execution_budget.remaining() == 0,
            });
            quantum_witnesses.push(QuantumWitness {
                time,
                subject: subject.clone(),
                outcome,
                resource: selected_index,
                charged,
            });
            sequential.complete_step(step, Some(selected_index), trace, &subject)?;
        } else {
            sequential.complete_step(step, None, trace, &subject)?;
        }
    }
    sequential.done_stuttering(trace, EXECUTION_SUBJECT)?;
    record_misses(&jobs, horizon, &mut misses);
    let completed_jobs = jobs
        .iter()
        .filter(|job| job.execution_budget.remaining() == 0)
        .count();
    let job_accounting = jobs
        .iter()
        .map(|job| JobAccounting {
            task_id: job.task_id.clone(),
            sequence: job.sequence,
            release: job.release,
            absolute_deadline: job.absolute_deadline,
            declared: job.execution_budget.capacity(),
            spent: job.execution_budget.spent(),
            dispatches: dispatches
                .iter()
                .filter(|dispatch| {
                    dispatch.task_id == job.task_id && dispatch.job_sequence == job.sequence
                })
                .count() as u64,
        })
        .collect();
    Ok(ScheduleResult {
        horizon,
        dispatches,
        misses,
        completed_jobs,
        quantum_witnesses,
        job_accounting,
        sequential_history: sequential.history().to_vec(),
    })
}

fn execute_task_set(
    tasks: &[TaskSpec],
    horizon: u64,
    trace: &mut TraceLog,
    control: EdfControl,
) -> Result<ScheduleResult, StructureError> {
    let releases = periodic_release_trace(tasks, horizon)?;
    execute_release_trace(tasks, &releases, horizon, trace, control)
}

pub fn run_periodic_case(
    tasks: &[TaskSpec],
    control: EdfControl,
) -> Result<EdfRun, StructureError> {
    let mut trace = TraceLog::default();
    let admission = admit_task_set(tasks, &mut trace, control)?;
    let schedule = if admission.admitted {
        let horizon = admission
            .certificate
            .as_ref()
            .ok_or_else(|| StructureError::new("admitted set has no certificate"))?
            .feasibility_bound;
        let registered_tasks = registered_tasks(&admission)?;
        Some(execute_task_set(
            &registered_tasks,
            horizon,
            &mut trace,
            control,
        )?)
    } else {
        None
    };
    Ok(EdfRun {
        admission,
        schedule,
        trace,
    })
}

fn registered_tasks(admission: &AdmissionDecision) -> Result<Vec<TaskSpec>, StructureError> {
    let registry = admission
        .registry
        .as_ref()
        .ok_or_else(|| StructureError::new("admitted set has no authoritative registry"))?;
    registry
        .ids()
        .map(|id| {
            registry
                .get(id)
                .cloned()
                .ok_or_else(|| StructureError::new("admitted registry lost a task record"))
        })
        .collect()
}

/// Bind the emitted Budget charge to this recipe's registered projection.
/// Formula separation is supplied by `edf_admission_reference`, not
/// by this structural trace check.
fn verify_admission_budget(
    trace: &TraceLog,
    subject: &str,
    capacity: u64,
    amount: u64,
    registry_commit: u64,
) -> Result<(), StructureError> {
    let initialize = trace.require_single_event_for(Structure::Budget, "Initialize", subject)?;
    let check = trace.require_single_event_for(Structure::Budget, "Check", subject)?;
    let commit = trace.require_single_event_for(Structure::Budget, "Commit", subject)?;
    if initialize.detail != format!("unit={} capacity={capacity}", ExecutionTicks::NAME) {
        return Err(StructureError::new(format!(
            "admission Budget.Initialize differs for {subject}"
        )));
    }
    if !check.detail.starts_with(&format!("amount={amount} "))
        || !commit.detail.starts_with(&format!("amount={amount} "))
    {
        return Err(StructureError::new(format!(
            "admission budget charge differs for {subject}"
        )));
    }
    if initialize.sequence >= check.sequence
        || check.sequence >= commit.sequence
        || commit.sequence >= registry_commit
    {
        return Err(StructureError::new(format!(
            "admission budget is not ordered before registry commit for {subject}"
        )));
    }
    Ok(())
}

/// Reconstruct readiness without using the candidate set captured by
/// `SelectThenActuate`.
///
/// This projection treats the dispatch log as its progress witness. Its
/// independence from the candidate set is valid only together with the
/// `spent == dispatches` Budget reconciliation in `verify_positive_recipe`.
/// Keep that reconciliation and this reconstruction in the same verifier.
fn expected_ready_resources(schedule: &ScheduleResult, time: u64) -> Vec<usize> {
    schedule
        .job_accounting
        .iter()
        .enumerate()
        .filter(|(_, account)| {
            if account.release > time {
                return false;
            }
            let prior_dispatches = schedule
                .dispatches
                .iter()
                .filter(|dispatch| {
                    dispatch.time < time
                        && dispatch.task_id == account.task_id
                        && dispatch.job_sequence == account.sequence
                })
                .count() as u64;
            prior_dispatches < account.declared
        })
        .map(|(resource, _)| resource)
        .collect()
}

pub fn run_sporadic_case(
    tasks: &[TaskSpec],
    releases: &[ReleaseEvent],
    horizon: u64,
    control: EdfControl,
) -> Result<EdfRun, StructureError> {
    let mut trace = TraceLog::default();
    let admission = admit_task_set(tasks, &mut trace, control)?;
    let schedule = if admission.admitted {
        let registered_tasks = registered_tasks(&admission)?;
        Some(execute_release_trace(
            &registered_tasks,
            releases,
            horizon,
            &mut trace,
            control,
        )?)
    } else {
        None
    };
    Ok(EdfRun {
        admission,
        schedule,
        trace,
    })
}

pub fn verify_positive_recipe(run: &EdfRun) -> Result<(), StructureError> {
    if !run.admission.admitted {
        return Err(StructureError::new("positive recipe was not admitted"));
    }
    let schedule = run
        .schedule
        .as_ref()
        .ok_or_else(|| StructureError::new("positive recipe has no schedule"))?;
    if !schedule.no_deadline_miss() {
        return Err(StructureError::new("positive recipe missed a deadline"));
    }
    let certificate = run
        .admission
        .certificate
        .as_ref()
        .ok_or_else(|| StructureError::new("positive recipe has no admission certificate"))?;
    if certificate.checked_intervals != certificate.feasibility_bound {
        return Err(StructureError::new(format!(
            "positive recipe checked {} of {} required intervals",
            certificate.checked_intervals, certificate.feasibility_bound
        )));
    }
    if run.admission.registry.is_none() {
        return Err(StructureError::new(
            "positive recipe has no authoritative task registry",
        ));
    }
    let registry_commit = run.trace.require_single_event_for(
        Structure::ResourceRegistry,
        "Commit",
        ADMISSION_SUBJECT,
    )?;
    let registered = registered_tasks(&run.admission)?;
    verify_admission_budget(
        &run.trace,
        &repeating_admission_subject(),
        certificate.hyperperiod,
        certificate.repeating_demand,
        registry_commit.sequence,
    )?;
    for interval in 1..=certificate.feasibility_bound {
        let demand = registered.iter().try_fold(0u64, |total, task| {
            total
                .checked_add(interval_demand(task, interval)?)
                .ok_or_else(|| StructureError::new("verification interval demand overflow"))
        })?;
        verify_admission_budget(
            &run.trace,
            &interval_admission_subject(interval),
            interval,
            demand,
            registry_commit.sequence,
        )?;
    }

    if schedule.sequential_history.len() != schedule.horizon as usize {
        return Err(StructureError::new(
            "sequential history does not cover every execution quantum",
        ));
    }
    if schedule.quantum_witnesses.len() != schedule.dispatches.len() {
        return Err(StructureError::new(
            "dispatch count does not match selection-actuation witnesses",
        ));
    }

    let mut witnessed_times = BTreeSet::new();
    for witness in &schedule.quantum_witnesses {
        if !witnessed_times.insert(witness.time) {
            return Err(StructureError::new(format!(
                "execution quantum {} has multiple witnesses",
                witness.time
            )));
        }
        if witness.subject != quantum_subject(witness.time) {
            return Err(StructureError::new(format!(
                "execution quantum {} has the wrong evidence identity",
                witness.time
            )));
        }
        let outcome = witness.outcome.as_ref().ok_or_else(|| {
            StructureError::new(format!(
                "execution quantum {} bypassed SelectThenActuate",
                witness.time
            ))
        })?;
        if outcome.resource() != witness.resource {
            return Err(StructureError::new(format!(
                "execution quantum {} did not actuate its selected resource",
                witness.time
            )));
        }
        let expected_ready = expected_ready_resources(schedule, witness.time);
        if outcome.candidates() != expected_ready {
            return Err(StructureError::new(format!(
                "execution quantum {} did not select from the complete ready set",
                witness.time
            )));
        }
        if witness.charged != 1 {
            return Err(StructureError::new(format!(
                "execution quantum {} charged {} units instead of one",
                witness.time, witness.charged
            )));
        }
        if schedule.sequential_history[witness.time as usize] != Some(witness.resource) {
            return Err(StructureError::new(format!(
                "execution quantum {} history does not name its selected resource",
                witness.time
            )));
        }
        run.trace.verify_recipe_instance_for(
            &witness.subject,
            &EXECUTION_STRUCTURES,
            &EXECUTION_EDGES,
        )?;
        for action in ["Check", "Commit"] {
            let budget =
                run.trace
                    .require_single_event_for(Structure::Budget, action, &witness.subject)?;
            if !budget.detail.starts_with("amount=1 ") {
                return Err(StructureError::new(format!(
                    "execution quantum {} has a non-unit Budget.{action}",
                    witness.time
                )));
            }
        }
        let actuation = run.trace.require_single_event_for(
            Structure::ActuationPass,
            "Commit",
            &witness.subject,
        )?;
        if !actuation
            .detail
            .contains(&format!("resource={}", witness.resource))
        {
            return Err(StructureError::new(format!(
                "execution quantum {} actuation trace names a different resource",
                witness.time
            )));
        }
        let dispatch = schedule
            .dispatches
            .iter()
            .find(|dispatch| dispatch.time == witness.time)
            .ok_or_else(|| {
                StructureError::new(format!(
                    "execution quantum {} has no dispatch record",
                    witness.time
                ))
            })?;
        let account = schedule
            .job_accounting
            .get(witness.resource)
            .ok_or_else(|| {
                StructureError::new(format!(
                    "execution quantum {} names an unknown job resource",
                    witness.time
                ))
            })?;
        if dispatch.task_id != account.task_id
            || dispatch.job_sequence != account.sequence
            || dispatch.absolute_deadline != account.absolute_deadline
        {
            return Err(StructureError::new(format!(
                "execution quantum {} dispatch record differs from its selected job",
                witness.time
            )));
        }
    }

    for time in 0..schedule.horizon {
        let subject = quantum_subject(time);
        let expected_ready = expected_ready_resources(schedule, time);
        let has_witness = witnessed_times.contains(&time);
        if expected_ready.is_empty() == has_witness {
            return Err(StructureError::new(format!(
                "execution quantum {time} violates work conservation"
            )));
        }
        let begin = run
            .trace
            .require_single_event_for(Structure::Sequential, "Begin", &subject)?;
        let complete =
            run.trace
                .require_single_event_for(Structure::Sequential, "Complete", &subject)?;
        if begin.sequence >= complete.sequence {
            return Err(StructureError::new(format!(
                "execution quantum {time} completes before it begins"
            )));
        }
        if schedule.sequential_history[time as usize].is_some() != has_witness {
            return Err(StructureError::new(format!(
                "execution quantum {time} history and dispatch evidence disagree"
            )));
        }
    }

    for account in &schedule.job_accounting {
        if account.spent != account.dispatches {
            return Err(StructureError::new(format!(
                "job {}#{} spent {} units across {} dispatches",
                account.task_id, account.sequence, account.spent, account.dispatches
            )));
        }
        if account.spent > account.declared {
            return Err(StructureError::new(format!(
                "job {}#{} exceeded its declared execution demand",
                account.task_id, account.sequence
            )));
        }
    }
    Ok(())
}

pub fn feasible_arbitrary_deadline_set() -> Vec<TaskSpec> {
    vec![
        TaskSpec::new("sensor", 1, 5, 3),
        TaskSpec::new("control", 1, 3, 4),
    ]
}

pub fn interval_overload_set() -> Vec<TaskSpec> {
    vec![
        TaskSpec::new("short", 2, 2, 5),
        TaskSpec::new("burst", 2, 3, 5),
    ]
}

pub fn urgency_sensitive_set() -> Vec<TaskSpec> {
    vec![
        TaskSpec::new("urgent", 2, 2, 4),
        TaskSpec::new("later", 1, 3, 4),
    ]
}

pub fn long_run_overload_set() -> Vec<TaskSpec> {
    vec![
        TaskSpec::new("left", 2, 3, 3),
        TaskSpec::new("right", 2, 3, 3),
    ]
}

pub fn expected_control_rejection(control: EdfControl) -> Option<&'static str> {
    match control {
        EdfControl::None => None,
        EdfControl::BypassAdmissionCharges
        | EdfControl::UtilizationOnly
        | EdfControl::ReverseUrgency
        | EdfControl::SuppressProgress => Some("positive recipe missed a deadline"),
        EdfControl::AccelerateProgress => Some("charged 2 units instead of one"),
        EdfControl::MisdirectActuation => Some("bypassed SelectThenActuate"),
        EdfControl::OmitReadyCandidate => Some("did not select from the complete ready set"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::references::{edf_admission_reference, edf_exhaustive_reference};

    #[test]
    fn exact_recipe_accepts_and_executes_arbitrary_deadlines() {
        let tasks = feasible_arbitrary_deadline_set();
        let run = run_periodic_case(&tasks, EdfControl::None).unwrap();
        assert!(run.admission.admitted);
        assert!(run.schedule.as_ref().unwrap().no_deadline_miss());
        assert_eq!(
            edf_admission_reference(&tasks).unwrap(),
            run.admission.admitted
        );
        assert!(edf_exhaustive_reference(&tasks, 12).unwrap());
        verify_positive_recipe(&run).unwrap();
    }

    #[test]
    fn admitted_sporadic_release_trace_meets_deadlines() {
        let tasks = vec![
            TaskSpec::new("sensor", 1, 3, 4),
            TaskSpec::new("control", 1, 2, 3),
        ];
        let releases = vec![
            ReleaseEvent::new(0, "sensor"),
            ReleaseEvent::new(1, "control"),
            ReleaseEvent::new(4, "control"),
            ReleaseEvent::new(5, "sensor"),
            ReleaseEvent::new(9, "control"),
            ReleaseEvent::new(10, "sensor"),
            ReleaseEvent::new(12, "control"),
        ];
        let run = run_sporadic_case(&tasks, &releases, 15, EdfControl::None).unwrap();
        assert!(run.admission.admitted);
        assert!(run.schedule.as_ref().unwrap().no_deadline_miss());
        verify_positive_recipe(&run).unwrap();
    }

    #[test]
    fn sporadic_release_trace_rejects_early_release() {
        let tasks = vec![TaskSpec::new("sensor", 1, 3, 4)];
        let releases = vec![
            ReleaseEvent::new(0, "sensor"),
            ReleaseEvent::new(3, "sensor"),
        ];
        assert!(run_sporadic_case(&tasks, &releases, 8, EdfControl::None)
            .unwrap_err()
            .to_string()
            .contains("requires 4"));
    }

    #[test]
    fn interval_demand_rejects_a_utilization_only_false_positive() {
        let tasks = interval_overload_set();
        let exact = run_periodic_case(&tasks, EdfControl::None).unwrap();
        let weakened = run_periodic_case(&tasks, EdfControl::UtilizationOnly).unwrap();
        assert!(!edf_admission_reference(&tasks).unwrap());
        assert!(!exact.admission.admitted);
        assert!(weakened.admission.admitted);
        assert!(!weakened.schedule.unwrap().no_deadline_miss());
    }

    #[test]
    fn positive_recipe_requires_complete_interval_coverage() {
        let tasks = feasible_arbitrary_deadline_set();
        let weakened = run_periodic_case(&tasks, EdfControl::UtilizationOnly).unwrap();
        assert!(weakened.admission.admitted);
        assert!(weakened.schedule.as_ref().unwrap().no_deadline_miss());
        assert!(verify_positive_recipe(&weakened)
            .unwrap_err()
            .to_string()
            .contains("required intervals"));
    }

    #[test]
    fn reverse_urgency_breaks_a_feasible_schedule() {
        let tasks = urgency_sensitive_set();
        let exact = run_periodic_case(&tasks, EdfControl::None).unwrap();
        let weakened = run_periodic_case(&tasks, EdfControl::ReverseUrgency).unwrap();
        assert!(edf_admission_reference(&tasks).unwrap());
        assert!(exact.schedule.unwrap().no_deadline_miss());
        assert!(!weakened.schedule.unwrap().no_deadline_miss());
    }

    #[test]
    fn bypassed_admission_accepts_long_run_overload() {
        let tasks = long_run_overload_set();
        let exact = run_periodic_case(&tasks, EdfControl::None).unwrap();
        let weakened = run_periodic_case(&tasks, EdfControl::BypassAdmissionCharges).unwrap();
        assert!(!edf_admission_reference(&tasks).unwrap());
        assert!(!exact.admission.admitted);
        assert!(weakened.admission.admitted);
        assert!(!weakened.schedule.unwrap().no_deadline_miss());
    }

    #[test]
    fn selected_work_without_progress_misses() {
        let tasks = feasible_arbitrary_deadline_set();
        let weakened = run_periodic_case(&tasks, EdfControl::SuppressProgress).unwrap();
        assert!(!weakened.schedule.as_ref().unwrap().no_deadline_miss());
        assert!(verify_positive_recipe(&weakened)
            .unwrap_err()
            .to_string()
            .contains("missed a deadline"));
    }

    #[test]
    fn accelerated_progress_cannot_pass_unit_accounting() {
        let tasks = vec![TaskSpec::new("work", 2, 2, 4)];
        let weakened = run_periodic_case(&tasks, EdfControl::AccelerateProgress).unwrap();
        assert!(weakened.schedule.as_ref().unwrap().no_deadline_miss());
        assert_eq!(weakened.schedule.as_ref().unwrap().dispatches.len(), 2);
        assert!(verify_positive_recipe(&weakened)
            .unwrap_err()
            .to_string()
            .contains("charged 2 units instead of one"));
    }

    #[test]
    fn misdirected_actuation_cannot_pass_the_shared_handoff() {
        let tasks = feasible_arbitrary_deadline_set();
        let weakened = run_periodic_case(&tasks, EdfControl::MisdirectActuation).unwrap();
        assert!(weakened.schedule.as_ref().unwrap().no_deadline_miss());
        assert!(verify_positive_recipe(&weakened)
            .unwrap_err()
            .to_string()
            .contains("bypassed SelectThenActuate"));
    }

    #[test]
    fn omitted_ready_candidate_cannot_pass_eligibility_binding() {
        let tasks = vec![
            TaskSpec::new("first", 1, 2, 4),
            TaskSpec::new("second", 1, 3, 4),
        ];
        let weakened = run_periodic_case(&tasks, EdfControl::OmitReadyCandidate).unwrap();
        assert!(weakened.schedule.as_ref().unwrap().no_deadline_miss());
        assert!(verify_positive_recipe(&weakened)
            .unwrap_err()
            .to_string()
            .contains("complete ready set"));
    }

    #[test]
    fn registered_controls_fail_for_their_registered_reason() {
        let cases = [
            (EdfControl::BypassAdmissionCharges, long_run_overload_set()),
            (EdfControl::UtilizationOnly, interval_overload_set()),
            (EdfControl::ReverseUrgency, urgency_sensitive_set()),
            (
                EdfControl::SuppressProgress,
                feasible_arbitrary_deadline_set(),
            ),
            (
                EdfControl::AccelerateProgress,
                vec![TaskSpec::new("work", 2, 2, 4)],
            ),
            (
                EdfControl::MisdirectActuation,
                feasible_arbitrary_deadline_set(),
            ),
            (
                EdfControl::OmitReadyCandidate,
                vec![
                    TaskSpec::new("first", 1, 2, 4),
                    TaskSpec::new("second", 1, 3, 4),
                ],
            ),
        ];
        for (control, tasks) in cases {
            let expected = expected_control_rejection(control).unwrap();
            let run = run_periodic_case(&tasks, control).unwrap();
            let observed = verify_positive_recipe(&run).unwrap_err().to_string();
            assert!(
                observed.contains(expected),
                "control {control:?} produced {observed:?}, expected text {expected:?}"
            );
        }
    }

    #[test]
    fn generated_admission_and_positive_recipes_match_their_claims() {
        let mut task_shapes = Vec::new();
        for period in 2..=5 {
            for deadline in 1..=6 {
                for wcet in 1..=3 {
                    task_shapes.push((wcet, deadline, period));
                }
            }
        }
        let mut compared = 0usize;
        let mut admitted = 0usize;
        for (left_index, left) in task_shapes.iter().enumerate() {
            for right in task_shapes.iter().skip(left_index).take(12) {
                let tasks = vec![
                    TaskSpec::new("left", left.0, left.1, left.2),
                    TaskSpec::new("right", right.0, right.1, right.2),
                ];
                let run = run_periodic_case(&tasks, EdfControl::None).unwrap();
                assert_eq!(
                    edf_admission_reference(&tasks).unwrap(),
                    run.admission.admitted,
                    "mismatch for {tasks:?}"
                );
                if run.admission.admitted {
                    admitted += 1;
                    let schedule = run.schedule.as_ref().unwrap();
                    assert!(schedule.no_deadline_miss(), "deadline miss for {tasks:?}");
                    assert!(schedule
                        .job_accounting
                        .iter()
                        .all(|job| job.absolute_deadline <= schedule.horizon));
                    assert!(schedule
                        .job_accounting
                        .iter()
                        .all(|job| job.spent == job.declared));
                    verify_positive_recipe(&run).unwrap();
                }
                compared += 1;
            }
        }
        assert_eq!(compared, 798);
        assert_eq!(admitted, 271);
    }

    #[test]
    fn bounded_edf_execution_agrees_with_exhaustive_feasibility() {
        let mut task_shapes = Vec::new();
        for period in 2..=4 {
            for deadline in 1..=5 {
                for wcet in 1..=2 {
                    task_shapes.push((wcet, deadline, period));
                }
            }
        }
        let mut compared = 0usize;
        for (left_index, left) in task_shapes.iter().enumerate() {
            for right in task_shapes.iter().skip(left_index).take(8) {
                let tasks = vec![
                    TaskSpec::new("left", left.0, left.1, left.2),
                    TaskSpec::new("right", right.0, right.1, right.2),
                ];
                let exhaustive = edf_exhaustive_reference(&tasks, 8).unwrap();
                let mut trace = TraceLog::default();
                let edf = execute_task_set(&tasks, 8, &mut trace, EdfControl::None).unwrap();
                assert_eq!(
                    exhaustive,
                    edf.no_deadline_miss(),
                    "bounded scheduling mismatch for {tasks:?}"
                );
                compared += 1;
            }
        }
        assert_eq!(compared, 212);
    }
}
