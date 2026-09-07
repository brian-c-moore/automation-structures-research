use crate::cicd_reference::{
    enumerate_schedules, expected_outputs, PipelineEvent, EXPECTED_SCHEDULE_COUNT,
};
use formal_example_structures::{
    ActuationPass, Budget, Edge, ForkJoin, RelationshipGraph, ResourceRegistry, Sequential,
    StepGraph, Structure, StructureError, TraceLog, TraversalEngine, Unit,
};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

const SUBJECT: &str = "FEX-DOM-CICD-01::pipeline";
const JOBS: [&str; 4] = ["compile", "static-analysis", "test-matrix", "package"];
const PARTITIONS: [&str; 2] = ["test-linux", "test-windows"];
const DECLARED_EDGES: [(usize, usize); 4] = [(0, 1), (0, 2), (1, 3), (2, 3)];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Compute;

impl Unit for Compute {
    const NAME: &'static str = "Compute";
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum CiCdControl {
    Honest,
    EarlyExecution,
    MissingCarrierPredecessor,
    SkipJoin,
    DropWorkerCompletion,
    FlattenToSequential,
    BypassDebit,
    MisdirectEffect,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct PipelineResult {
    pub outputs: BTreeSet<String>,
    pub compute_spent: u64,
    pub completed_jobs: usize,
    pub completed_workers: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ScheduleAgreement {
    pub reference_schedules: usize,
    pub construction_schedules: usize,
    pub mismatches: Vec<String>,
}

impl ScheduleAgreement {
    pub fn passed(&self) -> bool {
        self.mismatches.is_empty()
            && self.reference_schedules == EXPECTED_SCHEDULE_COUNT
            && self.construction_schedules == EXPECTED_SCHEDULE_COUNT
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct CiCdRun {
    pub control: CiCdControl,
    pub schedule: Vec<PipelineEvent>,
    pub result: PipelineResult,
    pub trace: TraceLog,
    declaration_edges: Vec<(usize, usize)>,
    carrier_edges: Vec<(usize, usize)>,
    carrier_states: Option<Vec<u8>>,
    worker_states: Option<Vec<u8>>,
    fork_phase: Option<u8>,
    fork_output_ready: Option<bool>,
    registry_ids: BTreeSet<String>,
    charged_units: BTreeMap<String, u64>,
    effect_targets: BTreeMap<String, String>,
}

fn job_subject(job: usize) -> String {
    format!("{SUBJECT}::job::{}", JOBS[job])
}

fn worker_subject(worker: usize) -> String {
    format!("{SUBJECT}::worker::{}", PARTITIONS[worker])
}

fn registry(trace: &mut TraceLog) -> Result<ResourceRegistry<String>, StructureError> {
    let records = JOBS
        .iter()
        .chain(PARTITIONS.iter())
        .map(|id| ((*id).to_string(), (*id).to_string()));
    ResourceRegistry::build(records, trace, SUBJECT)
}

fn declaration_graph(trace: &mut TraceLog) -> Result<RelationshipGraph, StructureError> {
    RelationshipGraph::build(
        JOBS.into_iter().map(str::to_string),
        DECLARED_EDGES
            .into_iter()
            .map(|(from, to)| Edge {
                from: JOBS[from].to_string(),
                to: JOBS[to].to_string(),
                weight: 1,
            })
            .collect(),
        trace,
        SUBJECT,
    )
}

fn traverse_declaration(
    graph: &RelationshipGraph,
    trace: &mut TraceLog,
) -> Result<BTreeSet<String>, StructureError> {
    let mut traversal = TraversalEngine::new(JOBS[0].to_string(), trace, SUBJECT);
    let mut discovered = BTreeSet::from([JOBS[0].to_string()]);
    let mut covered = BTreeSet::new();
    while !traversal.frontier().is_empty() {
        let item = traversal.visit_at(0, trace)?;
        let work_id = item.work_id();
        let vertex = item.into_payload();
        covered.insert(vertex.clone());
        for edge in graph.outgoing(&vertex) {
            if discovered.insert(edge.to.clone()) {
                traversal.enqueue(edge.to.clone(), trace);
            }
        }
        traversal.accept(work_id, trace)?;
    }
    traversal.finish(trace)?;
    Ok(covered)
}

#[derive(Clone, Copy)]
struct WorkEffect<'a> {
    logical_id: &'a str,
    amount: u64,
    target: usize,
}

impl<'a> WorkEffect<'a> {
    fn new(logical_id: &'a str, amount: u64, target: usize) -> Self {
        Self {
            logical_id,
            amount,
            target,
        }
    }
}

fn charge_and_apply(
    work: WorkEffect<'_>,
    budget: &mut Budget<Compute>,
    outputs: &mut [bool; 6],
    trace: &mut TraceLog,
    control: CiCdControl,
    charged_units: &mut BTreeMap<String, u64>,
    effect_targets: &mut BTreeMap<String, String>,
) -> Result<(), StructureError> {
    let WorkEffect {
        logical_id,
        amount,
        target,
    } = work;
    let subject = format!("{SUBJECT}::effect::{logical_id}");
    let actual_target =
        if control == CiCdControl::MisdirectEffect && logical_id == "static-analysis" {
            4
        } else {
            target
        };
    let mut pass = ActuationPass::new(vec![Some(actual_target)], trace, &subject);
    pass.actuate_with(
        0,
        outputs,
        |slot, trace, subject| {
            if !(control == CiCdControl::BypassDebit && logical_id == "package") {
                budget.try_reserve(amount, trace, subject)?;
            }
            *slot = true;
            Ok(())
        },
        trace,
        &subject,
    )?;
    pass.finish(trace, &subject)?;
    let charged = if control == CiCdControl::BypassDebit && logical_id == "package" {
        0
    } else {
        amount
    };
    charged_units.insert(logical_id.to_string(), charged);
    effect_targets.insert(logical_id.to_string(), output_id(actual_target).to_string());
    Ok(())
}

fn output_id(index: usize) -> &'static str {
    match index {
        0 => "compile",
        1 => "static-analysis",
        2 => "test-linux",
        3 => "test-windows",
        4 => "package",
        5 => "test-matrix",
        _ => "unknown",
    }
}

fn flattened_run(schedule: &[PipelineEvent]) -> Result<CiCdRun, StructureError> {
    let mut trace = TraceLog::default();
    let registered = registry(&mut trace)?;
    let declaration = declaration_graph(&mut trace)?;
    let covered = traverse_declaration(&declaration, &mut trace)?;
    if covered.len() != JOBS.len() {
        return Err(StructureError::new(
            "pipeline declaration is not fully reachable",
        ));
    }
    let mut budget = Budget::<Compute>::new(6, &mut trace, SUBJECT);
    let mut outputs = [false; 6];
    let mut charged_units = BTreeMap::new();
    let mut effect_targets = BTreeMap::new();
    let mut sequential = Sequential::new(
        schedule.len() as u64,
        None::<PipelineEvent>,
        &mut trace,
        SUBJECT,
    )?;
    for (index, event) in schedule.iter().enumerate() {
        let step_subject = format!("{SUBJECT}::flattened::{index}");
        let step = sequential.begin_step(&mut trace, &step_subject)?;
        match *event {
            PipelineEvent::CompleteJob(0) => charge_and_apply(
                WorkEffect::new("compile", 2, 0),
                &mut budget,
                &mut outputs,
                &mut trace,
                CiCdControl::FlattenToSequential,
                &mut charged_units,
                &mut effect_targets,
            )?,
            PipelineEvent::CompleteJob(1) => charge_and_apply(
                WorkEffect::new("static-analysis", 1, 1),
                &mut budget,
                &mut outputs,
                &mut trace,
                CiCdControl::FlattenToSequential,
                &mut charged_units,
                &mut effect_targets,
            )?,
            PipelineEvent::CompleteWorker(worker) => charge_and_apply(
                WorkEffect::new(PARTITIONS[worker], 1, worker + 2),
                &mut budget,
                &mut outputs,
                &mut trace,
                CiCdControl::FlattenToSequential,
                &mut charged_units,
                &mut effect_targets,
            )?,
            PipelineEvent::PublishTestOutput => outputs[5] = true,
            PipelineEvent::CompleteJob(3) => charge_and_apply(
                WorkEffect::new("package", 1, 4),
                &mut budget,
                &mut outputs,
                &mut trace,
                CiCdControl::FlattenToSequential,
                &mut charged_units,
                &mut effect_targets,
            )?,
            _ => {}
        }
        sequential.complete_step(step, Some(*event), &mut trace, &step_subject)?;
    }
    sequential.done_stuttering(&mut trace, SUBJECT)?;
    Ok(CiCdRun {
        control: CiCdControl::FlattenToSequential,
        schedule: schedule.to_vec(),
        result: PipelineResult {
            outputs: outputs
                .iter()
                .enumerate()
                .filter(|(_, present)| **present)
                .map(|(index, _)| output_id(index).to_string())
                .collect(),
            compute_spent: budget.spent(),
            completed_jobs: 4,
            completed_workers: 2,
        },
        trace,
        declaration_edges: DECLARED_EDGES.to_vec(),
        carrier_edges: Vec::new(),
        carrier_states: None,
        worker_states: None,
        fork_phase: None,
        fork_output_ready: None,
        registry_ids: registered.ids().cloned().collect(),
        charged_units,
        effect_targets,
    })
}

pub fn execute_schedule(
    schedule: &[PipelineEvent],
    control: CiCdControl,
) -> Result<CiCdRun, StructureError> {
    if control == CiCdControl::FlattenToSequential {
        return flattened_run(schedule);
    }
    let mut trace = TraceLog::default();
    let registered = registry(&mut trace)?;
    let declaration = declaration_graph(&mut trace)?;
    let covered = traverse_declaration(&declaration, &mut trace)?;
    if covered.len() != JOBS.len() {
        return Err(StructureError::new(
            "pipeline declaration is not fully reachable",
        ));
    }
    let carrier_edges = if control == CiCdControl::MissingCarrierPredecessor {
        vec![(0, 1), (0, 2), (1, 3)]
    } else {
        DECLARED_EDGES.to_vec()
    };
    let mut outer = StepGraph::new(4, carrier_edges.clone(), &mut trace, SUBJECT)?;
    let mut inner = ForkJoin::new(2, 2, 0, &mut trace, &job_subject(2))?;
    let mut budget = Budget::<Compute>::new(6, &mut trace, SUBJECT);
    let mut outputs = [false; 6];
    let mut charged_units = BTreeMap::new();
    let mut effect_targets = BTreeMap::new();

    for event in schedule {
        match *event {
            PipelineEvent::StartJob(job) => {
                if outer.state(job) == Some(0) {
                    outer.become_ready(job, &mut trace, &job_subject(job))?;
                }
                outer.start_running(job, &mut trace, &job_subject(job))?;
            }
            PipelineEvent::CompleteJob(job) => {
                if job == 0 {
                    charge_and_apply(
                        WorkEffect::new(JOBS[job], 2, 0),
                        &mut budget,
                        &mut outputs,
                        &mut trace,
                        control,
                        &mut charged_units,
                        &mut effect_targets,
                    )?;
                } else if job == 1 {
                    charge_and_apply(
                        WorkEffect::new(JOBS[job], 1, 1),
                        &mut budget,
                        &mut outputs,
                        &mut trace,
                        control,
                        &mut charged_units,
                        &mut effect_targets,
                    )?;
                } else if job == 3 {
                    charge_and_apply(
                        WorkEffect::new(JOBS[job], 1, 4),
                        &mut budget,
                        &mut outputs,
                        &mut trace,
                        control,
                        &mut charged_units,
                        &mut effect_targets,
                    )?;
                }
                outer.complete_node(job, &mut trace, &job_subject(job))?;
            }
            PipelineEvent::StartWorker(worker) => {
                if outer.state(2) != Some(2) {
                    return Err(StructureError::new(
                        "test worker cannot start before the outer test job is running",
                    ));
                }
                if !(control == CiCdControl::DropWorkerCompletion && worker == 1) {
                    inner.start_worker(worker, &mut trace, &worker_subject(worker))?;
                }
            }
            PipelineEvent::CompleteWorker(worker) => {
                if control == CiCdControl::DropWorkerCompletion && worker == 1 {
                    outputs[3] = true;
                } else {
                    inner.complete_worker(worker, 1, &mut trace, &worker_subject(worker))?;
                    charge_and_apply(
                        WorkEffect::new(PARTITIONS[worker], 1, worker + 2),
                        &mut budget,
                        &mut outputs,
                        &mut trace,
                        control,
                        &mut charged_units,
                        &mut effect_targets,
                    )?;
                }
            }
            PipelineEvent::Barrier => {
                if control != CiCdControl::SkipJoin && control != CiCdControl::DropWorkerCompletion
                {
                    inner.barrier(&mut trace, &job_subject(2))?;
                }
            }
            PipelineEvent::PublishTestOutput => {
                if control != CiCdControl::SkipJoin && control != CiCdControl::DropWorkerCompletion
                {
                    inner.produce_output(&mut trace, &job_subject(2))?;
                }
                outputs[5] = true;
            }
        }
    }
    if outer.states().iter().all(|state| *state == 3) {
        outer.done_stuttering(&mut trace, SUBJECT)?;
    }
    if inner.phase() == 2 {
        inner.done_stuttering(&mut trace, &job_subject(2))?;
    }
    let result = PipelineResult {
        outputs: outputs
            .iter()
            .enumerate()
            .filter(|(_, present)| **present)
            .map(|(index, _)| output_id(index).to_string())
            .collect(),
        compute_spent: budget.spent(),
        completed_jobs: outer.states().iter().filter(|state| **state == 3).count(),
        completed_workers: inner
            .worker_states()
            .iter()
            .filter(|state| **state == 2)
            .count(),
    };
    Ok(CiCdRun {
        control,
        schedule: schedule.to_vec(),
        result,
        trace,
        declaration_edges: DECLARED_EDGES.to_vec(),
        carrier_edges,
        carrier_states: Some(outer.states().to_vec()),
        worker_states: Some(inner.worker_states().to_vec()),
        fork_phase: Some(inner.phase()),
        fork_output_ready: Some(inner.output_ready()),
        registry_ids: registered.ids().cloned().collect(),
        charged_units,
        effect_targets,
    })
}

pub fn verify_pipeline_dag(run: &CiCdRun) -> Result<(), StructureError> {
    let expected_ids: BTreeSet<_> = JOBS
        .iter()
        .chain(PARTITIONS.iter())
        .map(|id| (*id).to_string())
        .collect();
    if run.registry_ids != expected_ids {
        return Err(StructureError::new(
            "pipeline resource registry is not exact",
        ));
    }
    if run.declaration_edges != DECLARED_EDGES || run.carrier_edges != DECLARED_EDGES {
        return Err(StructureError::new(
            "StepGraph carrier does not bind the declared dependency relation",
        ));
    }
    if run.carrier_states.as_deref() != Some(&[3, 3, 3, 3]) {
        return Err(StructureError::new(
            "outer pipeline did not complete every job",
        ));
    }
    let structures = run.trace.structures();
    for required in [
        Structure::ResourceRegistry,
        Structure::RelationshipGraph,
        Structure::TraversalEngine,
        Structure::StepGraph,
    ] {
        if !structures.contains(&required) {
            return Err(StructureError::new(format!(
                "missing load-bearing structure {}",
                required.name()
            )));
        }
    }
    Ok(())
}

pub fn verify_parallel_test_execution(run: &CiCdRun) -> Result<(), StructureError> {
    if run.worker_states.as_deref() != Some(&[2, 2])
        || run.fork_phase != Some(2)
        || run.fork_output_ready != Some(true)
    {
        return Err(StructureError::new(
            "test matrix did not complete both workers, cross the barrier, and publish output",
        ));
    }
    let expected_worker_charges = BTreeMap::from([
        ("test-linux".to_string(), 1),
        ("test-windows".to_string(), 1),
    ]);
    let observed_worker_charges: BTreeMap<_, _> = run
        .charged_units
        .iter()
        .filter(|(id, _)| id.starts_with("test-"))
        .map(|(id, charge)| (id.clone(), *charge))
        .collect();
    if observed_worker_charges != expected_worker_charges {
        return Err(StructureError::new(
            "test partition debit identity does not match declared work",
        ));
    }
    for partition in PARTITIONS {
        if !run.result.outputs.contains(partition) {
            return Err(StructureError::new(
                "joined test output omits a declared partition",
            ));
        }
    }
    let structures = run.trace.structures();
    for required in [
        Structure::ResourceRegistry,
        Structure::ForkJoin,
        Structure::Budget,
        Structure::ActuationPass,
    ] {
        if !structures.contains(&required) {
            return Err(StructureError::new(format!(
                "missing load-bearing structure {}",
                required.name()
            )));
        }
    }
    let barrier =
        run.trace
            .require_single_event_for(Structure::ForkJoin, "Barrier", &job_subject(2))?;
    let output = run.trace.require_single_event_for(
        Structure::ForkJoin,
        "ProduceOutput",
        &job_subject(2),
    )?;
    if barrier.sequence >= output.sequence {
        return Err(StructureError::new("test output preceded the join barrier"));
    }
    Ok(())
}

pub fn verify_run(run: &CiCdRun) -> Result<(), StructureError> {
    verify_pipeline_dag(run)?;
    verify_parallel_test_execution(run)?;
    let outer_start = run.trace.require_single_event_for(
        Structure::StepGraph,
        "StartRunning",
        &job_subject(2),
    )?;
    for worker in 0..PARTITIONS.len() {
        let worker_start = run.trace.require_single_event_for(
            Structure::ForkJoin,
            "StartWorker",
            &worker_subject(worker),
        )?;
        if outer_start.sequence >= worker_start.sequence {
            return Err(StructureError::new(
                "test worker started before the outer test job",
            ));
        }
    }
    let joined_output = run.trace.require_single_event_for(
        Structure::ForkJoin,
        "ProduceOutput",
        &job_subject(2),
    )?;
    let outer_complete = run.trace.require_single_event_for(
        Structure::StepGraph,
        "CompleteNode",
        &job_subject(2),
    )?;
    if joined_output.sequence >= outer_complete.sequence {
        return Err(StructureError::new(
            "outer test job completed before joined output publication",
        ));
    }
    let expected_charges = BTreeMap::from([
        ("compile".to_string(), 2),
        ("static-analysis".to_string(), 1),
        ("test-linux".to_string(), 1),
        ("test-windows".to_string(), 1),
        ("package".to_string(), 1),
    ]);
    if run.charged_units != expected_charges || run.result.compute_spent != 6 {
        return Err(StructureError::new(
            "compute debit identity does not match declared work",
        ));
    }
    if run
        .effect_targets
        .iter()
        .any(|(logical, actual)| logical != actual)
    {
        return Err(StructureError::new(
            "an effect was applied to the wrong resource",
        ));
    }
    if run.result.outputs != expected_outputs() {
        return Err(StructureError::new(
            "pipeline output set is incomplete or misdirected",
        ));
    }
    Ok(())
}

pub fn run(control: CiCdControl) -> Result<CiCdRun, StructureError> {
    let schedules = enumerate_schedules();
    let schedule = schedules
        .first()
        .ok_or_else(|| StructureError::new("reference enumerator returned no schedules"))?;
    if control == CiCdControl::EarlyExecution {
        let mut early = schedule.clone();
        let package_start = early
            .iter()
            .position(|event| *event == PipelineEvent::StartJob(3))
            .ok_or_else(|| StructureError::new("reference schedule omitted package start"))?;
        let compile_complete = early
            .iter()
            .position(|event| *event == PipelineEvent::CompleteJob(0))
            .ok_or_else(|| StructureError::new("reference schedule omitted compile completion"))?;
        let event = early.remove(package_start);
        early.insert(compile_complete + 1, event);
        execute_schedule(&early, control)
    } else {
        execute_schedule(schedule, control)
    }
}

#[derive(Clone)]
struct CarrierScheduleState {
    outer: StepGraph,
    inner: ForkJoin,
    trace: TraceLog,
}

impl CarrierScheduleState {
    fn initial() -> Result<Self, StructureError> {
        let mut trace = TraceLog::default();
        Ok(Self {
            outer: StepGraph::new(4, DECLARED_EDGES.to_vec(), &mut trace, "carrier-enumerator")?,
            inner: ForkJoin::new(2, 2, 0, &mut trace, "carrier-enumerator")?,
            trace,
        })
    }

    fn terminal(&self) -> bool {
        self.outer.states() == [3, 3, 3, 3]
            && self.inner.worker_states() == [2, 2]
            && self.inner.phase() == 2
            && self.inner.output_ready()
    }

    fn enabled(&self) -> Vec<PipelineEvent> {
        let mut events = Vec::new();
        for job in 0..4 {
            let state = self.outer.state(job);
            if state == Some(1) || (state == Some(0) && self.outer.predecessors_complete(job)) {
                events.push(PipelineEvent::StartJob(job));
            }
            if state == Some(2) && (job != 2 || self.inner.output_ready()) {
                events.push(PipelineEvent::CompleteJob(job));
            }
        }
        if self.outer.state(2) == Some(2) && self.inner.phase() == 0 {
            for worker in 0..2 {
                match self.inner.worker_states()[worker] {
                    0 => events.push(PipelineEvent::StartWorker(worker)),
                    1 => events.push(PipelineEvent::CompleteWorker(worker)),
                    _ => {}
                }
            }
            if self.inner.all_complete() {
                events.push(PipelineEvent::Barrier);
            }
        }
        if self.inner.phase() == 1 {
            events.push(PipelineEvent::PublishTestOutput);
        }
        events
    }

    fn apply(&mut self, event: PipelineEvent) -> Result<(), StructureError> {
        match event {
            PipelineEvent::StartJob(job) => {
                if self.outer.state(job) == Some(0) {
                    self.outer
                        .become_ready(job, &mut self.trace, "carrier-enumerator")?;
                }
                self.outer
                    .start_running(job, &mut self.trace, "carrier-enumerator")
            }
            PipelineEvent::CompleteJob(job) => {
                self.outer
                    .complete_node(job, &mut self.trace, "carrier-enumerator")
            }
            PipelineEvent::StartWorker(worker) => {
                self.inner
                    .start_worker(worker, &mut self.trace, "carrier-enumerator")
            }
            PipelineEvent::CompleteWorker(worker) => {
                self.inner
                    .complete_worker(worker, 1, &mut self.trace, "carrier-enumerator")
            }
            PipelineEvent::Barrier => self.inner.barrier(&mut self.trace, "carrier-enumerator"),
            PipelineEvent::PublishTestOutput => self
                .inner
                .produce_output(&mut self.trace, "carrier-enumerator"),
        }
    }
}

fn enumerate_carrier_from(
    state: CarrierScheduleState,
    prefix: &mut Vec<PipelineEvent>,
    schedules: &mut Vec<Vec<PipelineEvent>>,
) -> Result<(), StructureError> {
    if state.terminal() {
        schedules.push(prefix.clone());
        return Ok(());
    }
    for event in state.enabled() {
        let mut next = state.clone();
        next.apply(event)?;
        prefix.push(event);
        enumerate_carrier_from(next, prefix, schedules)?;
        prefix.pop();
    }
    Ok(())
}

fn enumerate_carrier_schedules() -> Result<Vec<Vec<PipelineEvent>>, StructureError> {
    let mut schedules = Vec::new();
    enumerate_carrier_from(
        CarrierScheduleState::initial()?,
        &mut Vec::new(),
        &mut schedules,
    )?;
    schedules.sort();
    schedules.dedup();
    Ok(schedules)
}

pub fn compare_all_schedules() -> ScheduleAgreement {
    let reference = enumerate_schedules();
    let construction = match enumerate_carrier_schedules() {
        Ok(schedules) => schedules,
        Err(error) => {
            return ScheduleAgreement {
                reference_schedules: reference.len(),
                construction_schedules: 0,
                mismatches: vec![format!("carrier enumeration failed: {error}")],
            };
        }
    };
    let reference_set: BTreeSet<_> = reference.iter().cloned().collect();
    let construction_set: BTreeSet<_> = construction.iter().cloned().collect();
    let mut mismatches = Vec::new();
    if reference.len() != EXPECTED_SCHEDULE_COUNT {
        mismatches.push(format!(
            "reference enumerator produced {} schedules; expected {EXPECTED_SCHEDULE_COUNT}",
            reference.len()
        ));
    }
    if construction.len() != EXPECTED_SCHEDULE_COUNT {
        mismatches.push(format!(
            "carrier enumerator produced {} schedules; expected {EXPECTED_SCHEDULE_COUNT}",
            construction.len()
        ));
    }
    for schedule in reference_set.difference(&construction_set).take(8) {
        mismatches.push(format!(
            "reference schedule missing from carriers: {schedule:?}"
        ));
    }
    for schedule in construction_set.difference(&reference_set).take(8) {
        mismatches.push(format!(
            "carrier schedule absent from reference: {schedule:?}"
        ));
    }
    for (index, schedule) in reference.iter().enumerate() {
        match execute_schedule(schedule, CiCdControl::Honest) {
            Ok(run) => match verify_run(&run) {
                Ok(()) if run.result.outputs == expected_outputs() => {}
                Ok(()) => mismatches.push(format!("schedule {index} produced a different output")),
                Err(error) => {
                    mismatches.push(format!("schedule {index} failed verification: {error}"))
                }
            },
            Err(error) => mismatches.push(format!("schedule {index} was rejected: {error}")),
        }
    }
    ScheduleAgreement {
        reference_schedules: reference.len(),
        construction_schedules: construction.len(),
        mismatches,
    }
}

pub fn expected_control_rejection(control: CiCdControl) -> Option<&'static str> {
    match control {
        CiCdControl::Honest => None,
        CiCdControl::EarlyExecution => Some("cannot become ready before every predecessor"),
        CiCdControl::MissingCarrierPredecessor => Some("StepGraph carrier does not bind"),
        CiCdControl::SkipJoin | CiCdControl::DropWorkerCompletion => {
            Some("test matrix did not complete")
        }
        CiCdControl::FlattenToSequential => Some("StepGraph carrier does not bind"),
        CiCdControl::BypassDebit => Some("compute debit identity"),
        CiCdControl::MisdirectEffect => Some("wrong resource"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_independently_enumerated_schedule_is_accepted() {
        let agreement = compare_all_schedules();
        assert!(agreement.passed(), "{:?}", agreement.mismatches);
    }

    #[test]
    fn honest_pipeline_uses_both_authoritative_carriers() {
        let run = run(CiCdControl::Honest).unwrap();
        verify_run(&run).unwrap();
        assert_eq!(run.result.outputs, expected_outputs());
        assert_eq!(run.result.compute_spent, 6);
    }

    #[test]
    fn early_execution_is_rejected_by_step_graph() {
        assert!(run(CiCdControl::EarlyExecution).is_err());
    }

    #[test]
    fn inner_worker_cannot_start_before_the_outer_test_job() {
        let error = execute_schedule(
            &[
                PipelineEvent::StartJob(0),
                PipelineEvent::CompleteJob(0),
                PipelineEvent::StartWorker(0),
            ],
            CiCdControl::Honest,
        )
        .unwrap_err();
        assert!(error.to_string().contains("outer test job is running"));
    }

    #[test]
    fn premise_and_seam_controls_cannot_pass_verification() {
        for control in [
            CiCdControl::MissingCarrierPredecessor,
            CiCdControl::SkipJoin,
            CiCdControl::DropWorkerCompletion,
            CiCdControl::FlattenToSequential,
            CiCdControl::BypassDebit,
            CiCdControl::MisdirectEffect,
        ] {
            let run = run(control).unwrap();
            assert!(verify_run(&run).is_err(), "control {control:?} escaped");
        }
    }

    #[test]
    fn flattening_can_reproduce_the_output_but_not_the_recipe() {
        let run = run(CiCdControl::FlattenToSequential).unwrap();
        assert_eq!(run.result.outputs, expected_outputs());
        assert!(verify_run(&run).is_err());
    }
}
