use formal_example_algorithms::{
    self as algorithms, evidence as algorithm_evidence, AlgorithmFault, AlgorithmRun,
};
use formal_example_domains::{
    cicd::{self, CiCdControl, PipelineResult},
    crdt::{
        self, concurrent_delete_assign_script, observed_delete_with_stale_delivery_script,
        observed_overwrite_script, offline_different_paths_script,
        published_concurrent_assignment_script, CrdtControl, ScriptStep,
    },
    edf::{self, verify_positive_recipe, EdfControl, EdfRun, TaskSpec},
    evidence as domain_evidence,
    lod::{self, LodFault, LodOutput},
    ospf::{self, OspfFault, OspfOutput},
    rdp::{
        self, demonstration_requests, AccountantConfig, AccountantControl, DEFAULT_EPSILON_CEILING,
    },
    references::{edf_admission_reference, edf_reference_bundle},
    relation::{self, RelationReport, RelationSpec},
    stm::{
        self, atomic_pair_case, conflicting_writers_case, early_publication_case,
        undeclared_access_case, StmControl,
    },
    ExampleRun,
};
use formal_example_structures::{MaterializedDacRecord, MemoizationControl};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::process::ExitCode;

const MANIFEST_SOURCE: &str = include_str!("../../../../manifest.json");

#[derive(Debug, Deserialize, Serialize)]
struct Manifest {
    schema: String,
    examples: Vec<ManifestEntry>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct ManifestEntry {
    id: String,
    name: String,
    family: String,
    claim: String,
    limits: Vec<String>,
}

#[derive(Serialize)]
struct ComparisonBundle {
    evidence: formal_example_structures::MaterializedDacRecord,
    lod: ExampleRun<LodOutput>,
    ospf_conventional: ExampleRun<OspfOutput>,
    ospf_rooted_frontier: ExampleRun<OspfOutput>,
    relation: RelationReport,
}

#[derive(Serialize)]
struct Description {
    public: ManifestEntry,
    evidence: formal_example_structures::MaterializedDacRecord,
}

#[derive(Serialize)]
struct EdfBundle {
    id: String,
    scenario: String,
    control: EdfControl,
    tasks: Vec<TaskSpec>,
    separate_admission: bool,
    exhaustive_prefix_feasible: Option<bool>,
    verifier_accepted: bool,
    verifier_error: Option<String>,
    run: EdfRun,
}

#[derive(Serialize)]
struct CrdtBundle {
    id: String,
    scenario: String,
    control: String,
    verifier_accepted: bool,
    construction_error: Option<String>,
    verifier_error: Option<String>,
    issued_operations: usize,
    edit_steps: usize,
    captured_states: usize,
    deliveries: usize,
    replica_operation_counts: BTreeMap<String, usize>,
    views: BTreeMap<String, String>,
    structural_events: usize,
}

#[derive(Serialize)]
struct RdpAccountView {
    accepted_queries: usize,
    reported_epsilon: u64,
    winner_alpha: Option<u64>,
    cumulative_curve: Vec<u64>,
}

#[derive(Serialize)]
struct RdpBundle {
    id: String,
    control: String,
    verifier_accepted: bool,
    construction_error: Option<String>,
    verifier_error: Option<String>,
    orders: Vec<u64>,
    scale: u64,
    delta: String,
    epsilon_ceiling: u64,
    requests: usize,
    accepted: usize,
    rejected: usize,
    accounts: BTreeMap<String, RdpAccountView>,
    structural_events: usize,
}

#[derive(Serialize)]
struct StmTransactionView {
    id: String,
    status: String,
    start_epoch: u64,
    begin_sequence: u64,
    end_sequence: Option<u64>,
    operations: usize,
}

#[derive(Serialize)]
struct StmBundle {
    id: String,
    scenario: String,
    control: String,
    verifier_accepted: bool,
    construction_error: Option<String>,
    verifier_error: Option<String>,
    opacity_accepted: bool,
    serialization: Vec<String>,
    final_heap: BTreeMap<String, i64>,
    final_epoch: u64,
    transactions: Vec<StmTransactionView>,
    exposed_reads: usize,
    applied_writes: usize,
    structural_events: usize,
}

#[derive(Serialize)]
struct CiCdBundle {
    id: String,
    control: String,
    verifier_accepted: bool,
    construction_error: Option<String>,
    verifier_error: Option<String>,
    result: Option<PipelineResult>,
    reference_schedules: usize,
    construction_schedules: usize,
    schedule_mismatches: Vec<String>,
    structural_events: usize,
}

fn manifest() -> Result<Manifest, String> {
    let manifest: Manifest = serde_json::from_str(MANIFEST_SOURCE)
        .map_err(|error| format!("invalid embedded manifest: {error}"))?;
    if manifest.schema != "formal-examples-manifest-v1" {
        return Err(format!("unknown manifest schema {}", manifest.schema));
    }
    let ids: BTreeSet<_> = manifest
        .examples
        .iter()
        .map(|example| example.id.as_str())
        .collect();
    if manifest.examples.is_empty() || ids.len() != manifest.examples.len() {
        return Err("manifest must contain unique examples".to_string());
    }
    let domain_registry = domain_evidence::registry()?;
    let algorithm_registry = algorithm_evidence::registry()?;
    let evidence_ids: BTreeSet<_> = domain_registry
        .ids()
        .into_iter()
        .chain(algorithm_registry.ids())
        .collect();
    let manifest_ids: BTreeSet<_> = manifest
        .examples
        .iter()
        .map(|example| example.id.clone())
        .collect();
    if evidence_ids != manifest_ids {
        return Err("manifest and executable evidence IDs differ".to_string());
    }
    for example in &manifest.examples {
        let record = describe_evidence(&example.id)?;
        let family = serde_json::to_value(&record.record.family)
            .map_err(|error| format!("cannot serialize evidence family: {error}"))?;
        if record.record.name != example.name
            || family.as_str() != Some(example.family.as_str())
            || record.record.boundary.claim != example.claim
        {
            return Err(format!(
                "manifest identity or claim differs from executable evidence for {}",
                example.id
            ));
        }
    }
    Ok(manifest)
}

fn describe_evidence(id: &str) -> Result<MaterializedDacRecord, String> {
    if let Ok(record) = domain_evidence::describe(id) {
        return Ok(record);
    }
    algorithm_evidence::describe(id)
}

fn format_json<T: Serialize>(value: &T) -> Result<(), String> {
    println!(
        "{}",
        serde_json::to_string_pretty(value)
            .map_err(|error| format!("cannot serialize output: {error}"))?
    );
    Ok(())
}

fn require_control_rejection(
    example: &str,
    control: &str,
    expected: &str,
    construction_error: Option<&str>,
    verifier_error: Option<&str>,
) -> Result<(), String> {
    let observed = construction_error
        .or(verifier_error)
        .ok_or_else(|| format!("{example} control {control} did not produce a rejection"))?;
    if observed.contains(expected) {
        Ok(())
    } else {
        Err(format!(
            "{example} control {control} produced the wrong rejection: expected text {expected:?}, observed {observed:?}"
        ))
    }
}

fn serialized_label<T: Serialize>(value: &T) -> Result<String, String> {
    serde_json::to_value(value)
        .map_err(|error| format!("cannot serialize label: {error}"))?
        .as_str()
        .map(str::to_string)
        .ok_or_else(|| "serialized label is not a string".to_string())
}

fn print_checks<T>(run: &ExampleRun<T>) {
    for check in &run.checks {
        println!(
            "  [{}] {}: {}",
            if check.passed { "PASS" } else { "FAIL" },
            check.name,
            check.detail
        );
    }
}

fn print_lod(run: &ExampleRun<LodOutput>) {
    println!("{} scenario={}", run.id, run.scenario);
    println!(
        "selected bytes={} utility={}",
        run.output.total_bytes, run.output.total_utility
    );
    for choice in &run.output.selected {
        println!(
            "  {} -> {} bytes={} weighted_utility={}",
            choice.object_id, choice.level_id, choice.bytes, choice.weighted_utility
        );
    }
    print_checks(run);
    println!("structural events={}", run.trace.events().len());
}

fn print_ospf(run: &ExampleRun<OspfOutput>) {
    println!("{} scenario={}", run.id, run.scenario);
    println!("destination | cost | next hops");
    for route in &run.output.routes {
        println!(
            "{} | {} | {}",
            route.destination,
            route.cost,
            route.next_hops.join(",")
        );
    }
    print_checks(run);
    println!("structural events={}", run.trace.events().len());
}

fn print_algorithm(run: &AlgorithmRun) {
    println!("{} {} scenario={}", run.id, run.name, run.scenario);
    println!("output={:?} reference={:?}", run.output, run.reference);
    for check in &run.checks {
        println!(
            "  [{}] {}: {}",
            if check.passed { "PASS" } else { "FAIL" },
            check.name,
            check.detail
        );
    }
    println!(
        "states admitted={} stored={} structural events={}",
        run.admitted_states,
        run.stored_states,
        run.trace.events().len()
    );
}

fn edf_control(args: &[String]) -> Result<EdfControl, String> {
    match option(args, "--control").as_deref().unwrap_or("none") {
        "none" => Ok(EdfControl::None),
        "bypass-admission" => Ok(EdfControl::BypassAdmissionCharges),
        "utilization-only" => Ok(EdfControl::UtilizationOnly),
        "reverse-urgency" => Ok(EdfControl::ReverseUrgency),
        "suppress-progress" => Ok(EdfControl::SuppressProgress),
        "accelerate-progress" => Ok(EdfControl::AccelerateProgress),
        "misdirect-actuation" => Ok(EdfControl::MisdirectActuation),
        "omit-ready-candidate" => Ok(EdfControl::OmitReadyCandidate),
        value => Err(format!("unknown EDF control {value}")),
    }
}

fn edf_scenario(
    name: Option<&str>,
    control: EdfControl,
) -> Result<(String, Vec<TaskSpec>), String> {
    let selected = name.unwrap_or(match control {
        EdfControl::BypassAdmissionCharges => "long-run-overload",
        EdfControl::UtilizationOnly => "interval-overload",
        EdfControl::ReverseUrgency => "urgency-sensitive",
        EdfControl::AccelerateProgress => "accelerated-progress",
        EdfControl::OmitReadyCandidate => "ready-set",
        EdfControl::None | EdfControl::SuppressProgress | EdfControl::MisdirectActuation => {
            "arbitrary-deadline"
        }
    });
    let tasks = match selected {
        "arbitrary-deadline" => edf::feasible_arbitrary_deadline_set(),
        "interval-overload" => edf::interval_overload_set(),
        "urgency-sensitive" => edf::urgency_sensitive_set(),
        "long-run-overload" => edf::long_run_overload_set(),
        "accelerated-progress" => vec![TaskSpec::new("work", 2, 2, 4)],
        "ready-set" => vec![
            TaskSpec::new("first", 1, 2, 4),
            TaskSpec::new("second", 1, 3, 4),
        ],
        value => return Err(format!("unknown EDF scenario {value}")),
    };
    Ok((selected.to_string(), tasks))
}

fn run_edf(args: &[String]) -> Result<(), String> {
    let control = edf_control(args)?;
    let (scenario, tasks) = edf_scenario(option(args, "--scenario").as_deref(), control)?;
    let run = edf::run_periodic_case(&tasks, control).map_err(|error| error.to_string())?;
    let horizon = run
        .admission
        .certificate
        .as_ref()
        .map(|certificate| certificate.feasibility_bound);
    let (separate_admission, exhaustive) = match horizon {
        Some(value) if value <= 24 => {
            let reference = edf_reference_bundle(&tasks, value)?;
            (
                reference.admission,
                Some(reference.exhaustive_prefix_feasible),
            )
        }
        _ => (edf_admission_reference(&tasks)?, None),
    };
    let verifier_error = verify_positive_recipe(&run)
        .err()
        .map(|error| error.to_string());
    let verifier_accepted = verifier_error.is_none();
    if control == EdfControl::None && !verifier_accepted {
        return Err(format!(
            "FEX-DOM-RT-01 positive recipe failed: {}",
            verifier_error
                .as_deref()
                .unwrap_or("unknown verifier error")
        ));
    }
    if control != EdfControl::None && verifier_accepted {
        return Err(format!(
            "FEX-DOM-RT-01 control {control:?} escaped the recipe verifier"
        ));
    }
    if let Some(expected) = edf::expected_control_rejection(control) {
        require_control_rejection(
            "FEX-DOM-RT-01",
            &serialized_label(&control)?,
            expected,
            None,
            verifier_error.as_deref(),
        )?;
    }
    let bundle = EdfBundle {
        id: "FEX-DOM-RT-01".to_string(),
        scenario,
        control,
        tasks,
        separate_admission,
        exhaustive_prefix_feasible: exhaustive,
        verifier_accepted,
        verifier_error,
        run,
    };
    if wants_json(args) {
        return format_json(&bundle);
    }
    println!(
        "{} scenario={} control={:?}",
        bundle.id, bundle.scenario, bundle.control
    );
    println!("separate admission={}", bundle.separate_admission);
    println!(
        "recipe admitted={} verifier accepted={}",
        bundle.run.admission.admitted, bundle.verifier_accepted
    );
    if let Some(schedule) = &bundle.run.schedule {
        println!(
            "horizon={} dispatches={} completed={} deadline misses={}",
            schedule.horizon,
            schedule.dispatches.len(),
            schedule.completed_jobs,
            schedule.misses.len()
        );
    }
    if let Some(value) = bundle.exhaustive_prefix_feasible {
        println!("exhaustive prefix feasible={value}");
    }
    if let Some(error) = &bundle.verifier_error {
        println!("expected verifier rejection: {error}");
    }
    println!("structural events={}", bundle.run.trace.events().len());
    Ok(())
}

fn crdt_control(args: &[String]) -> Result<(CrdtControl, String), String> {
    let name = option(args, "--control").unwrap_or_else(|| "none".to_string());
    let control = match name.as_str() {
        "none" => CrdtControl::Honest,
        "reuse-operation-identity" => CrdtControl::ReuseOperationIdentity,
        "bypass-reduction" => CrdtControl::BypassReduction,
        "left-biased-merge" => CrdtControl::LeftBiasedMerge,
        "duplicate-as-fresh" => CrdtControl::DuplicateAsFresh,
        "drop-causal-context" => CrdtControl::DropCausalContext,
        "lose-concurrent-value" => CrdtControl::LoseConcurrentValue,
        "drop-delete" => CrdtControl::DropDelete,
        "misdirect-delivery" => CrdtControl::MisdirectDelivery,
        "incomplete-convergence" => CrdtControl::IncompleteConvergence,
        "misorder-later-delivery" => CrdtControl::MisorderLaterDelivery,
        value => return Err(format!("unknown CRDT control {value}")),
    };
    Ok((control, name))
}

fn crdt_scenario(name: Option<&str>) -> Result<(String, Vec<ScriptStep>), String> {
    let selected = name.unwrap_or("concurrent-assignment");
    let steps = match selected {
        "concurrent-assignment" => published_concurrent_assignment_script("B", "C"),
        "offline-paths" => offline_different_paths_script(),
        "observed-overwrite" => observed_overwrite_script(),
        "observed-delete" => observed_delete_with_stale_delivery_script(),
        "concurrent-delete-assign" => concurrent_delete_assign_script(),
        value => return Err(format!("unknown CRDT scenario {value}")),
    };
    Ok((selected.to_string(), steps))
}

fn run_crdt(args: &[String]) -> Result<(), String> {
    let (control, control_name) = crdt_control(args)?;
    let requested_scenario = option(args, "--scenario");
    let default_scenario = match control {
        CrdtControl::DropCausalContext => "observed-overwrite",
        CrdtControl::DropDelete => "observed-delete",
        _ => "concurrent-assignment",
    };
    let (scenario, steps) =
        crdt_scenario(requested_scenario.as_deref().or(Some(default_scenario)))?;
    let attempted = crdt::run_script(&["p", "q"], &steps, control);
    let bundle = match attempted {
        Err(error) if control != CrdtControl::Honest => CrdtBundle {
            id: "FEX-DOM-DIST-01".to_string(),
            scenario,
            control: control_name,
            verifier_accepted: false,
            construction_error: Some(error.to_string()),
            verifier_error: None,
            issued_operations: 0,
            edit_steps: 0,
            captured_states: 0,
            deliveries: 0,
            replica_operation_counts: BTreeMap::new(),
            views: BTreeMap::new(),
            structural_events: 0,
        },
        Err(error) => return Err(format!("FEX-DOM-DIST-01 construction failed: {error}")),
        Ok(run) => {
            let verifier_error = crdt::verify_run(&run).err().map(|error| error.to_string());
            let verifier_accepted = verifier_error.is_none();
            if control == CrdtControl::Honest && !verifier_accepted {
                return Err(format!(
                    "FEX-DOM-DIST-01 positive recipe failed: {}",
                    verifier_error
                        .as_deref()
                        .unwrap_or("unknown verifier error")
                ));
            }
            if control != CrdtControl::Honest && verifier_accepted {
                return Err(format!(
                    "FEX-DOM-DIST-01 control {control:?} escaped the recipe verifier"
                ));
            }
            CrdtBundle {
                id: "FEX-DOM-DIST-01".to_string(),
                scenario,
                control: control_name,
                verifier_accepted,
                construction_error: None,
                verifier_error,
                issued_operations: run.issued_operations.len(),
                edit_steps: run.edit_witnesses.len(),
                captured_states: run.capture_witnesses.len(),
                deliveries: run.delivery_witnesses.len(),
                replica_operation_counts: run
                    .replicas
                    .iter()
                    .map(|(id, state)| (id.clone(), state.operation_count()))
                    .collect(),
                views: run
                    .observed_views
                    .iter()
                    .map(|(id, view)| (id.clone(), format!("{view:?}")))
                    .collect(),
                structural_events: run.trace.events().len(),
            }
        }
    };
    if let Some(expected) = crdt::expected_control_rejection(control) {
        require_control_rejection(
            &bundle.id,
            &bundle.control,
            expected,
            bundle.construction_error.as_deref(),
            bundle.verifier_error.as_deref(),
        )?;
    }
    if wants_json(args) {
        return format_json(&bundle);
    }
    println!(
        "{} scenario={} control={}",
        bundle.id, bundle.scenario, bundle.control
    );
    println!("verifier accepted={}", bundle.verifier_accepted);
    if let Some(error) = &bundle.construction_error {
        println!("expected construction rejection: {error}");
    }
    if let Some(error) = &bundle.verifier_error {
        println!("expected verifier rejection: {error}");
    }
    println!(
        "issued={} edits={} captures={} deliveries={}",
        bundle.issued_operations, bundle.edit_steps, bundle.captured_states, bundle.deliveries
    );
    for (replica, count) in &bundle.replica_operation_counts {
        println!("replica {replica}: operations={count}");
        if let Some(view) = bundle.views.get(replica) {
            println!("  view={view}");
        }
    }
    println!("structural events={}", bundle.structural_events);
    Ok(())
}

fn rdp_control(args: &[String]) -> Result<(AccountantControl, String), String> {
    let name = option(args, "--control").unwrap_or_else(|| "none".to_string());
    let control = match name.as_str() {
        "none" => AccountantControl::Honest,
        "reuse-query-identity" => AccountantControl::ReuseQueryIdentity,
        "omit-order-charge" => AccountantControl::OmitOrderCharge,
        "double-order-charge" => AccountantControl::DoubleOrderCharge,
        "drop-delta-penalty" => AccountantControl::DropDeltaPenalty,
        "omit-best-order" => AccountantControl::OmitBestOrderCandidate,
        "sum-standalone-bounds" => AccountantControl::SumPerQueryConvertedBounds,
        "bypass-reported-budget" => AccountantControl::BypassReportedBudget,
        "misdirect-account" => AccountantControl::MisdirectAccount,
        "mutate-rejected-state" => AccountantControl::MutateRejectedState,
        "misorder-later-commit" => AccountantControl::MisorderLaterCommit,
        value => return Err(format!("unknown RDP control {value}")),
    };
    Ok((control, name))
}

fn run_rdp(args: &[String]) -> Result<(), String> {
    let (control, control_name) = rdp_control(args)?;
    let config =
        AccountantConfig::fixed(DEFAULT_EPSILON_CEILING).map_err(|error| error.to_string())?;
    let requests = demonstration_requests(&config).map_err(|error| error.to_string())?;
    let attempted = rdp::run_workload(&["scope-a", "scope-b"], &config, &requests, control);
    let bundle = match attempted {
        Err(error) if control != AccountantControl::Honest => RdpBundle {
            id: "FEX-DOM-PRIV-01".to_string(),
            control: control_name,
            verifier_accepted: false,
            construction_error: Some(error.to_string()),
            verifier_error: None,
            orders: config.orders().to_vec(),
            scale: config.scale(),
            delta: config.delta_description().to_string(),
            epsilon_ceiling: config.epsilon_ceiling(),
            requests: requests.len(),
            accepted: 0,
            rejected: 0,
            accounts: BTreeMap::new(),
            structural_events: 0,
        },
        Err(error) => return Err(format!("FEX-DOM-PRIV-01 construction failed: {error}")),
        Ok(run) => {
            let verifier_error = rdp::verify_run(&run).err().map(|error| error.to_string());
            let verifier_accepted = verifier_error.is_none();
            if control == AccountantControl::Honest && !verifier_accepted {
                return Err(format!(
                    "FEX-DOM-PRIV-01 positive recipe failed: {}",
                    verifier_error
                        .as_deref()
                        .unwrap_or("unknown verifier error")
                ));
            }
            if control != AccountantControl::Honest && verifier_accepted {
                return Err(format!(
                    "FEX-DOM-PRIV-01 control {control:?} escaped the recipe verifier"
                ));
            }
            let accounts = ["scope-a", "scope-b"]
                .into_iter()
                .map(|account_id| {
                    let account = run.account(account_id).expect("registered account");
                    (
                        account_id.to_string(),
                        RdpAccountView {
                            accepted_queries: account.accepted_queries,
                            reported_epsilon: account.reported_epsilon,
                            winner_alpha: account.winner_alpha,
                            cumulative_curve: account.cumulative_curve,
                        },
                    )
                })
                .collect();
            RdpBundle {
                id: "FEX-DOM-PRIV-01".to_string(),
                control: control_name,
                verifier_accepted,
                construction_error: None,
                verifier_error,
                orders: config.orders().to_vec(),
                scale: config.scale(),
                delta: config.delta_description().to_string(),
                epsilon_ceiling: config.epsilon_ceiling(),
                requests: run.request_count(),
                accepted: run.accepted_count(),
                rejected: run.rejected_count(),
                accounts,
                structural_events: run.trace.events().len(),
            }
        }
    };
    if let Some(expected) = rdp::expected_control_rejection(control) {
        require_control_rejection(
            &bundle.id,
            &bundle.control,
            expected,
            bundle.construction_error.as_deref(),
            bundle.verifier_error.as_deref(),
        )?;
    }
    if wants_json(args) {
        return format_json(&bundle);
    }
    println!("{} control={}", bundle.id, bundle.control);
    println!(
        "orders={:?} scale={} delta={} ceiling={}",
        bundle.orders, bundle.scale, bundle.delta, bundle.epsilon_ceiling
    );
    println!(
        "requests={} accepted={} rejected={} verifier accepted={}",
        bundle.requests, bundle.accepted, bundle.rejected, bundle.verifier_accepted
    );
    if let Some(error) = &bundle.construction_error {
        println!("expected construction rejection: {error}");
    }
    if let Some(error) = &bundle.verifier_error {
        println!("expected verifier rejection: {error}");
    }
    for (id, account) in &bundle.accounts {
        println!(
            "account {id}: accepted={} epsilon={} alpha={:?} curve={:?}",
            account.accepted_queries,
            account.reported_epsilon,
            account.winner_alpha,
            account.cumulative_curve
        );
    }
    println!("structural events={}", bundle.structural_events);
    Ok(())
}

fn cicd_control(args: &[String]) -> Result<(CiCdControl, String), String> {
    let name = option(args, "--control").unwrap_or_else(|| "none".to_string());
    let control = match name.as_str() {
        "none" => CiCdControl::Honest,
        "early-execution" => CiCdControl::EarlyExecution,
        "missing-carrier-predecessor" => CiCdControl::MissingCarrierPredecessor,
        "skip-join" => CiCdControl::SkipJoin,
        "drop-worker-completion" => CiCdControl::DropWorkerCompletion,
        "flatten-to-sequential" => CiCdControl::FlattenToSequential,
        "bypass-debit" => CiCdControl::BypassDebit,
        "misdirect-effect" => CiCdControl::MisdirectEffect,
        value => return Err(format!("unknown CI/CD control {value}")),
    };
    Ok((control, name))
}

fn run_cicd(id: &str, args: &[String]) -> Result<(), String> {
    let (control, control_name) = cicd_control(args)?;
    let agreement = cicd::compare_all_schedules();
    if !agreement.passed() {
        return Err(format!(
            "{id} schedule-set comparison failed: {}",
            agreement.mismatches.join("; ")
        ));
    }
    let attempted = cicd::run(control);
    let bundle = match attempted {
        Err(error) if control != CiCdControl::Honest => CiCdBundle {
            id: id.to_string(),
            control: control_name,
            verifier_accepted: false,
            construction_error: Some(error.to_string()),
            verifier_error: None,
            result: None,
            reference_schedules: agreement.reference_schedules,
            construction_schedules: agreement.construction_schedules,
            schedule_mismatches: agreement.mismatches,
            structural_events: 0,
        },
        Err(error) => return Err(format!("{id} construction failed: {error}")),
        Ok(run) => {
            let verifier_error = cicd::verify_run(&run).err().map(|error| error.to_string());
            let verifier_accepted = verifier_error.is_none();
            if control == CiCdControl::Honest && !verifier_accepted {
                return Err(format!(
                    "{id} positive recipe failed: {}",
                    verifier_error
                        .as_deref()
                        .unwrap_or("unknown verifier error")
                ));
            }
            if control != CiCdControl::Honest && verifier_accepted {
                return Err(format!(
                    "{id} control {control:?} escaped the recipe verifier"
                ));
            }
            CiCdBundle {
                id: id.to_string(),
                control: control_name,
                verifier_accepted,
                construction_error: None,
                verifier_error,
                result: Some(run.result),
                reference_schedules: agreement.reference_schedules,
                construction_schedules: agreement.construction_schedules,
                schedule_mismatches: agreement.mismatches,
                structural_events: run.trace.events().len(),
            }
        }
    };
    if let Some(expected) = cicd::expected_control_rejection(control) {
        require_control_rejection(
            &bundle.id,
            &bundle.control,
            expected,
            bundle.construction_error.as_deref(),
            bundle.verifier_error.as_deref(),
        )?;
    }
    if wants_json(args) {
        return format_json(&bundle);
    }
    println!("{} control={}", bundle.id, bundle.control);
    println!(
        "accepted schedules: reference={} carriers={} mismatches={}",
        bundle.reference_schedules,
        bundle.construction_schedules,
        bundle.schedule_mismatches.len()
    );
    println!("verifier accepted={}", bundle.verifier_accepted);
    if let Some(error) = &bundle.construction_error {
        println!("expected construction rejection: {error}");
    }
    if let Some(error) = &bundle.verifier_error {
        println!("expected verifier rejection: {error}");
    }
    if let Some(result) = &bundle.result {
        println!(
            "jobs={} workers={} compute={} outputs={:?}",
            result.completed_jobs, result.completed_workers, result.compute_spent, result.outputs
        );
    }
    println!("structural events={}", bundle.structural_events);
    Ok(())
}

fn stm_control(args: &[String]) -> Result<(StmControl, String), String> {
    let name = option(args, "--control").unwrap_or_else(|| "none".to_string());
    let control = match name.as_str() {
        "none" => StmControl::Honest,
        "reuse-transaction-identity" => StmControl::ReuseTransactionIdentity,
        "undeclared-access" => StmControl::UndeclaredAccess,
        "ignore-epoch-validation" => StmControl::IgnoreEpochValidation,
        "allow-conflicting-commit" => StmControl::AllowConflictingCommit,
        "omit-write-target" => StmControl::OmitWriteTarget,
        "misdirect-write" => StmControl::MisdirectWrite,
        "publish-before-all-writes" => StmControl::PublishBeforeAllWrites,
        "partial-abort-after-write" => StmControl::PartialAbortAfterWrite,
        value => return Err(format!("unknown STM control {value}")),
    };
    Ok((control, name))
}

fn run_stm(args: &[String]) -> Result<(), String> {
    let (control, control_name) = stm_control(args)?;
    let default_scenario = match control {
        StmControl::AllowConflictingCommit | StmControl::ReuseTransactionIdentity => {
            "conflicting-writers"
        }
        StmControl::UndeclaredAccess => "undeclared-access",
        StmControl::PublishBeforeAllWrites => "early-publication",
        _ => "atomic-pair",
    };
    let scenario = option(args, "--scenario").unwrap_or_else(|| default_scenario.to_string());
    let (cells, transactions, steps) = match scenario.as_str() {
        "atomic-pair" => atomic_pair_case(),
        "conflicting-writers" => conflicting_writers_case(),
        "early-publication" => early_publication_case(),
        "undeclared-access" => undeclared_access_case(),
        value => return Err(format!("unknown STM scenario {value}")),
    };
    let attempted = stm::run_script(&cells, &transactions, &steps, control);
    let bundle = match attempted {
        Err(error) if control != StmControl::Honest => StmBundle {
            id: "FEX-DOM-TXN-01".to_string(),
            scenario,
            control: control_name,
            verifier_accepted: false,
            construction_error: Some(error.to_string()),
            verifier_error: None,
            opacity_accepted: false,
            serialization: Vec::new(),
            final_heap: BTreeMap::new(),
            final_epoch: 0,
            transactions: Vec::new(),
            exposed_reads: 0,
            applied_writes: 0,
            structural_events: 0,
        },
        Err(error) => return Err(format!("FEX-DOM-TXN-01 construction failed: {error}")),
        Ok(run) => {
            let opacity = run.opacity();
            let verifier_error = stm::verify_run(&run).err().map(|error| error.to_string());
            let verifier_accepted = verifier_error.is_none();
            if control == StmControl::Honest && !verifier_accepted {
                return Err(format!(
                    "FEX-DOM-TXN-01 positive recipe failed: {}",
                    verifier_error
                        .as_deref()
                        .unwrap_or("unknown verifier error")
                ));
            }
            if control != StmControl::Honest && verifier_accepted {
                return Err(format!(
                    "FEX-DOM-TXN-01 control {control:?} escaped the recipe verifier"
                ));
            }
            StmBundle {
                id: "FEX-DOM-TXN-01".to_string(),
                scenario,
                control: control_name,
                verifier_accepted,
                construction_error: None,
                verifier_error,
                opacity_accepted: opacity.accepted,
                serialization: opacity.serialization,
                final_heap: run.heap(),
                final_epoch: run.final_epoch,
                transactions: run
                    .transactions()
                    .into_iter()
                    .map(|record| StmTransactionView {
                        id: record.id,
                        status: format!("{:?}", record.status),
                        start_epoch: record.start_epoch,
                        begin_sequence: record.begin_sequence,
                        end_sequence: record.end_sequence,
                        operations: record.operations.len(),
                    })
                    .collect(),
                exposed_reads: run.reads.len(),
                applied_writes: run.applied_writes.len(),
                structural_events: run.trace.events().len(),
            }
        }
    };
    if let Some(expected) = stm::expected_control_rejection(control) {
        require_control_rejection(
            &bundle.id,
            &bundle.control,
            expected,
            bundle.construction_error.as_deref(),
            bundle.verifier_error.as_deref(),
        )?;
    }
    if wants_json(args) {
        return format_json(&bundle);
    }
    println!(
        "{} scenario={} control={}",
        bundle.id, bundle.scenario, bundle.control
    );
    println!(
        "verifier accepted={} opacity accepted={} serialization={:?}",
        bundle.verifier_accepted, bundle.opacity_accepted, bundle.serialization
    );
    if let Some(error) = &bundle.construction_error {
        println!("expected construction rejection: {error}");
    }
    if let Some(error) = &bundle.verifier_error {
        println!("expected verifier rejection: {error}");
    }
    println!(
        "heap={:?} epoch={} reads={} writes={}",
        bundle.final_heap, bundle.final_epoch, bundle.exposed_reads, bundle.applied_writes
    );
    for transaction in &bundle.transactions {
        println!(
            "transaction {}: status={} epoch={} begin={} end={:?} operations={}",
            transaction.id,
            transaction.status,
            transaction.start_epoch,
            transaction.begin_sequence,
            transaction.end_sequence,
            transaction.operations
        );
    }
    println!("structural events={}", bundle.structural_events);
    Ok(())
}

fn option(args: &[String], name: &str) -> Option<String> {
    args.windows(2)
        .find(|pair| pair[0] == name)
        .map(|pair| pair[1].clone())
}

fn wants_json(args: &[String]) -> bool {
    option(args, "--format").as_deref() == Some("json")
}

fn command_list(args: &[String]) -> Result<(), String> {
    let manifest = manifest()?;
    if wants_json(args) {
        return format_json(&manifest.examples);
    }
    for example in manifest.examples {
        println!("{} | {} | {}", example.id, example.family, example.name);
    }
    Ok(())
}

fn command_describe(args: &[String]) -> Result<(), String> {
    let id = args
        .first()
        .ok_or_else(|| "describe requires an artifact ID".to_string())?;
    let example = manifest()?
        .examples
        .into_iter()
        .find(|example| &example.id == id)
        .ok_or_else(|| format!("unknown formal example {id}"))?;
    let evidence = describe_evidence(id)?;
    let description = Description {
        public: example,
        evidence,
    };
    if wants_json(args) {
        return format_json(&description);
    }
    println!("{}: {}", description.public.id, description.public.name);
    println!("family: {}", description.public.family);
    println!("claim: {}", description.public.claim);
    println!(
        "construction outcome: {}",
        serialized_label(&description.evidence.record.construction.outcome)?
    );
    println!(
        "supports reconstruction: {}",
        description
            .evidence
            .record
            .construction
            .outcome
            .supports_reconstruction()
    );
    for inherited in &description.evidence.inherited_from {
        println!("inherits: {inherited}");
    }
    for behavior in &description.evidence.record.territory.included_behavior {
        println!("included behavior: {behavior}");
    }
    for role in &description.evidence.record.stripped_roles {
        println!(
            "role {}: {} ({})",
            role.role, role.domain_binding, role.preserved_relation
        );
    }
    for node in &description.evidence.record.construction.nodes {
        println!(
            "node {} [{}]: {}",
            node.id,
            serialized_label(&node.stratum)?,
            node.implementation_identity
        );
    }
    for edge in &description.evidence.record.construction.edges {
        println!(
            "edge {} -> {}: {}",
            edge.before, edge.after, edge.obligation
        );
    }
    if let Some(oracle) = &description.evidence.record.oracle {
        println!("oracle {}: {}", oracle.id, oracle.method);
        println!("equivalence: {}", oracle.equivalence_relation);
    }
    for control in &description.evidence.record.controls {
        println!(
            "control {} [{}]: {}",
            control.id,
            serialized_label(&control.class)?,
            control.target
        );
    }
    for limit in &description.public.limits {
        println!("limit: {limit}");
    }
    for falsifier in &description.evidence.record.boundary.falsifiers {
        println!("falsifier: {falsifier}");
    }
    Ok(())
}

fn command_run(args: &[String]) -> Result<(), String> {
    let id = args
        .first()
        .ok_or_else(|| "run requires an artifact ID".to_string())?;
    let scenario_name = option(args, "--scenario");
    match id.as_str() {
        "FEX-DOM-REN-03" | "FEX-ASM-01" => {
            let scenario_name = scenario_name.unwrap_or_else(|| "budget-cut".to_string());
            let input = lod::scenario(&scenario_name)
                .ok_or_else(|| format!("unknown LOD scenario {scenario_name}"))?;
            let mut run = lod::run_lod(&scenario_name, &input, LodFault::None)
                .map_err(|error| error.to_string())?;
            run.id = id.clone();
            if !run.passed() {
                return Err(format!("{id} failed one or more checks"));
            }
            if wants_json(args) {
                format_json(&run)
            } else {
                print_lod(&run);
                Ok(())
            }
        }
        "FEX-OSPF-001" => {
            let scenario_name = scenario_name.unwrap_or_else(|| "rfc2328-rt6".to_string());
            let input = ospf::scenario(&scenario_name)
                .ok_or_else(|| format!("unknown OSPF scenario {scenario_name}"))?;
            let implementation =
                option(args, "--implementation").unwrap_or_else(|| "rooted-frontier".to_string());
            let run = match implementation.as_str() {
                "rooted-frontier" => ospf::run_ospf(&scenario_name, &input, OspfFault::None),
                "conventional" => {
                    ospf::run_ospf_conventional(&scenario_name, &input, OspfFault::None)
                }
                _ => return Err(format!("unknown OSPF implementation {implementation}")),
            }
            .map_err(|error| error.to_string())?;
            if !run.passed() {
                return Err(format!("{id} failed one or more checks"));
            }
            if wants_json(args) {
                format_json(&run)
            } else {
                print_ospf(&run);
                Ok(())
            }
        }
        "FEX-XFER-LOD-OSPF-01" => {
            Err("run the LOD/OSPF relation with the compare command".to_string())
        }
        "FEX-DOM-RT-01" => run_edf(args),
        "FEX-DOM-CICD-01" | "FEX-DOM-CICD-03" | "FEX-ASM-06" => run_cicd(id, args),
        "FEX-DOM-DIST-01" => run_crdt(args),
        "FEX-DOM-PRIV-01" => run_rdp(args),
        "FEX-DOM-TXN-01" => run_stm(args),
        algorithms::schema::ID => {
            let run = algorithms::schema::run(MemoizationControl::None)
                .map_err(|error| error.to_string())?;
            if !run.passed() {
                return Err(format!("{id} failed one or more checks"));
            }
            if wants_json(args) {
                format_json(&run)
            } else {
                println!("{} scenario={}", run.id, run.scenario);
                println!("output={:?} reference={:?}", run.output, run.reference);
                for check in &run.checks {
                    println!(
                        "  [{}] {}: {}",
                        if check.passed { "PASS" } else { "FAIL" },
                        check.name,
                        check.detail
                    );
                }
                println!(
                    "states admitted={} stored={} structural events={}",
                    run.admitted_states,
                    run.stored_states,
                    run.trace.events().len()
                );
                Ok(())
            }
        }
        algorithm_id if algorithms::ALGORITHM_IDS.contains(&algorithm_id) => {
            let run = algorithms::run(
                algorithm_id,
                scenario_name.as_deref(),
                MemoizationControl::None,
                AlgorithmFault::None,
            )?;
            if !run.passed() {
                return Err(format!("{id} failed one or more checks"));
            }
            if wants_json(args) {
                format_json(&run)
            } else {
                print_algorithm(&run);
                Ok(())
            }
        }
        _ => Err(format!("unknown executable example {id}")),
    }
}

fn command_compare(args: &[String]) -> Result<(), String> {
    let relation_id = if args.first().map(String::as_str) == Some("FEX-XFER-LOD-OSPF-01") {
        "FEX-XFER-LOD-OSPF-01".to_string()
    } else {
        if args.len() < 2 || args[0] != "FEX-DOM-REN-03" || args[1] != "FEX-OSPF-001" {
            return Err(
                "compare requires a relation ID or FEX-DOM-REN-03 FEX-OSPF-001".to_string(),
            );
        }
        option(args, "--relation")
            .ok_or_else(|| "member-form compare requires --relation".to_string())?
    };
    if relation_id != "FEX-XFER-LOD-OSPF-01" {
        return Err(format!("unknown relation {relation_id}"));
    }
    let lod_input = lod::scenario("budget-cut").expect("built-in LOD scenario");
    let ospf_input = ospf::scenario("rfc2328-rt6").expect("built-in OSPF scenario");
    let lod = lod::run_lod("budget-cut", &lod_input, LodFault::None)
        .map_err(|error| error.to_string())?;
    let ospf_conventional =
        ospf::run_ospf_conventional("rfc2328-rt6", &ospf_input, OspfFault::None)
            .map_err(|error| error.to_string())?;
    let ospf_rooted_frontier = ospf::run_ospf("rfc2328-rt6", &ospf_input, OspfFault::None)
        .map_err(|error| error.to_string())?;
    let relation = relation::compare(&lod, &ospf_rooted_frontier, &RelationSpec::registered());
    if !relation.passed {
        return Err(format!("relation failed: {}", relation.errors.join("; ")));
    }
    let evidence = domain_evidence::describe(&relation_id)?;
    let bundle = ComparisonBundle {
        evidence,
        lod,
        ospf_conventional,
        ospf_rooted_frontier,
        relation,
    };
    if wants_json(args) {
        return format_json(&bundle);
    }
    println!("LOD rooted-frontier composition");
    print_lod(&bundle.lod);
    println!();
    println!("OSPF conventional composition");
    print_ospf(&bundle.ospf_conventional);
    println!();
    println!("OSPF rooted-frontier composition");
    print_ospf(&bundle.ospf_rooted_frontier);
    println!();
    println!("{} PASS", bundle.relation.id);
    println!(
        "assurance: {}",
        serialized_label(
            &bundle
                .evidence
                .record
                .relation
                .as_ref()
                .expect("registered relation evidence")
                .assurance_class
        )?
    );
    println!("shared nodes: {}", bundle.relation.shared_nodes.join(", "));
    println!("shared edges: {}", bundle.relation.shared_edges.join(", "));
    println!("LOD-only: {}", bundle.relation.lod_only.join(", "));
    println!("OSPF-only: {}", bundle.relation.ospf_only.join(", "));
    for residual in &bundle.relation.residuals {
        println!("residual: {residual}");
    }
    Ok(())
}

fn usage() {
    eprintln!("formal-example-runner list [--format json]");
    eprintln!("formal-example-runner describe ID [--format json]");
    eprintln!(
        "formal-example-runner run ID [--scenario NAME] [--implementation rooted-frontier|conventional] [--control NAME] [--format json]"
    );
    eprintln!("Memoization IDs accept named scenarios such as baseline or generated-0000.");
    eprintln!("FEX-DOM-RT-01 accepts the controls listed in its case-study README.");
    eprintln!("The CI/CD examples accept the controls listed in their case-study README.");
    eprintln!(
        "FEX-DOM-DIST-01 accepts the scenarios and controls listed in its case-study README."
    );
    eprintln!("FEX-DOM-PRIV-01 accepts the controls listed in its case-study README.");
    eprintln!("FEX-DOM-TXN-01 accepts the scenarios and controls listed in its case-study README.");
    eprintln!(
        "formal-example-runner compare FEX-DOM-REN-03 FEX-OSPF-001 --relation FEX-XFER-LOD-OSPF-01 [--format json]"
    );
    eprintln!("formal-example-runner compare FEX-XFER-LOD-OSPF-01 [--format json]");
}

fn main() -> ExitCode {
    let mut args: Vec<String> = env::args().skip(1).collect();
    let Some(command) = args.first().cloned() else {
        usage();
        return ExitCode::from(2);
    };
    args.remove(0);
    let result = match command.as_str() {
        "list" => command_list(&args),
        "describe" => command_describe(&args),
        "run" => command_run(&args),
        "compare" => command_compare(&args),
        _ => {
            usage();
            Err(format!("unknown command {command}"))
        }
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(1)
        }
    }
}
