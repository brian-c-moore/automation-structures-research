//! Test harness for the four implemented workloads.
//!
//! Reads a `FrameworkConfig`, instantiates a `ConfigVector`, looks
//! up the workload by name, and dispatches it through the chosen
//! modality driver. Decides between cross-modality output comparison
//! and `trace_properties` assertion based on the workload's declared
//! equivalence classes.
//!
//! Data pipeline, actor message exchange, build DAG, and scientific
//! workflow implement the `Workload` trait. Other workload names are
//! outside this harness and return `Fail`.

use crate::config::FrameworkConfig;
use crate::modalities::Modality;
use crate::policies::{
    ConfigVector, DependencyPolicy, EntityModel, InvocationPolicy, LifecyclePolicy, TopologyPolicy,
};
use crate::workloads::actor_message_exchange::MessageExchangeWorkload;
use crate::workloads::build_dag::BuildDagWorkload;
use crate::workloads::data_pipeline::DataPipelineWorkload;
use crate::workloads::scientific_workflow::{RecoveryStrategy, WorkflowDagWorkload};
use crate::workloads::Workload;

#[derive(Debug)]
pub enum HarnessOutcome {
    Pass(String),
    Fail(String),
}

/// Exact workload variants supported by this harness.
pub enum WorkloadKind {
    DataPipeline(DataPipelineWorkload),
    MessageExchange(MessageExchangeWorkload),
    BuildDag(BuildDagWorkload),
    WorkflowDag(WorkflowDagWorkload),
}

pub fn run_one(cfg: &FrameworkConfig) -> HarnessOutcome {
    if let Err(e) = cfg.validate() {
        return HarnessOutcome::Fail(format!("invalid config: {}", e));
    }
    let modality = match Modality::parse(&cfg.modality) {
        Ok(m) => m,
        Err(e) => return HarnessOutcome::Fail(format!("modality parse: {}", e)),
    };
    let cv = match build_config_vector(cfg) {
        Ok(c) => c,
        Err(e) => return HarnessOutcome::Fail(format!("config: {}", e)),
    };
    let kind = match lookup_workload(&cfg.workload) {
        Ok(k) => k,
        Err(e) => return HarnessOutcome::Fail(format!("workload: {}", e)),
    };
    dispatch(&kind, modality, &cv)
}

fn dispatch(kind: &WorkloadKind, m: Modality, cv: &ConfigVector) -> HarnessOutcome {
    match kind {
        WorkloadKind::DataPipeline(w) => run_workload(w, m, cv),
        WorkloadKind::MessageExchange(w) => run_workload(w, m, cv),
        WorkloadKind::BuildDag(w) => run_workload(w, m, cv),
        WorkloadKind::WorkflowDag(w) => run_workload(w, m, cv),
    }
}

fn build_config_vector(cfg: &FrameworkConfig) -> Result<ConfigVector, String> {
    Ok(ConfigVector {
        invocation: parse_invocation(&cfg.policies.invocation)?,
        entity_model: EntityModel::parse(&cfg.policies.entity_model)?,
        topology: parse_topology(&cfg.policies.topology)?,
        dependencies: parse_dependency(&cfg.policies.dependencies)?,
        lifecycle: parse_lifecycle(&cfg.policies.lifecycle)?,
    })
}

fn lookup_workload(name: &str) -> Result<WorkloadKind, String> {
    match name {
        "data_pipeline" =>
            Ok(WorkloadKind::DataPipeline(DataPipelineWorkload::default_with(6))),
        "actor_message_exchange" | "message_exchange" =>
            Ok(WorkloadKind::MessageExchange(MessageExchangeWorkload::default_with(5))),
        "build_dag" =>
            Ok(WorkloadKind::BuildDag(BuildDagWorkload::small_example())),
        // Default to Airflow-flavor (RerunFromFailure) recovery. The
        // Airflow-vs-Temporal difference is observable in the workload's
        // `recovery_events` output, which requires constructing both variants
        // directly.
        "scientific_workflow" | "workflow_dag" =>
            Ok(WorkloadKind::WorkflowDag(
                WorkflowDagWorkload::small_example_with(RecoveryStrategy::RerunFromFailure))),
        other =>
            Err(format!("unsupported workload `{}`; supported names are data_pipeline, actor_message_exchange, build_dag, and scientific_workflow", other)),
    }
}

/// Pick the reference modality for cross-modality output comparison.
/// If Sequential is compatible, use it; otherwise use the first
/// modality of the workload's first equivalence class.
fn reference_modality<W: Workload>(w: &W) -> Modality {
    let compatible = w.compatible_modalities();
    if compatible.contains(&Modality::Sequential) {
        Modality::Sequential
    } else {
        w.equivalence_classes()
            .first()
            .and_then(|cls| cls.first())
            .copied()
            .expect("workload declares no compatible modalities; trait violated")
    }
}

pub fn run_workload<W: Workload>(w: &W, m: Modality, cv: &ConfigVector) -> HarnessOutcome
where
    W::OpId: Ord,
{
    if !w.compatible_modalities().contains(&m) {
        return HarnessOutcome::Fail(format!("workload not compatible with modality {:?}", m));
    }

    let actual = match run_with(w, m, cv) {
        Ok(o) => o,
        Err(outcome) => return outcome,
    };

    let ref_m = reference_modality(w);
    let same_class = w
        .equivalence_classes()
        .iter()
        .any(|cls| cls.contains(&m) && cls.contains(&ref_m));
    let cross_modal_reference_available = same_class && m != ref_m;

    if cross_modal_reference_available {
        let expected = match run_with(w, ref_m, cv) {
            Ok(o) => o,
            Err(outcome) => return outcome,
        };
        return if actual == expected {
            HarnessOutcome::Pass(format!(
                "modality={:?} output matches cross-modality reference={:?} output",
                m, ref_m
            ))
        } else {
            HarnessOutcome::Fail(format!(
                "modality={:?} output {:?} != reference={:?} output {:?}",
                m, actual, ref_m, expected
            ))
        };
    }

    // Either target is in its own equivalence class OR target == reference
    // (single-compatible-modality workload). Both cases require
    // trace_properties to verify the output; no cross-modality comparison
    // is available.
    let properties = w.trace_properties(cv);
    if properties.is_empty() {
        return HarnessOutcome::Fail(format!(
            "modality {:?} is in its own equivalence class and workload \
             declares no trace_properties; harness has nothing to assert",
            m
        ));
    }
    let failures: Vec<usize> = properties
        .iter()
        .enumerate()
        .filter(|(_, p)| !p(&actual))
        .map(|(i, _)| i)
        .collect();
    if failures.is_empty() {
        HarnessOutcome::Pass(format!(
            "modality={:?} passes {} trace properties",
            m,
            properties.len()
        ))
    } else {
        HarnessOutcome::Fail(format!(
            "modality={:?} fails trace_properties indexes {:?} (of {})",
            m,
            failures,
            properties.len()
        ))
    }
}

fn run_with<W: Workload>(w: &W, m: Modality, cv: &ConfigVector) -> Result<W::Output, HarnessOutcome>
where
    W::OpId: Ord,
{
    match m {
        Modality::Sequential => Ok(crate::modalities::sequential::run_sequential(w, cv)),
        Modality::ForkJoin => Ok(crate::modalities::fork_join::run_fork_join(w, cv)),
        Modality::StepGraph => crate::modalities::step_graph::run_step_graph(w, cv)
            .map_err(|e| HarnessOutcome::Fail(format!("step-graph driver: {:?}", e))),
        Modality::StreamGraph => Ok(crate::modalities::stream_graph::run_stream_graph(w, cv)),
    }
}

// ----- Policy parse helpers (string -> typed enum). -----

fn parse_invocation(s: &str) -> Result<InvocationPolicy, String> {
    match s {
        // Strictly-typed values understood by the policies module.
        "FIFO" | "Fifo" | "fifo" => Ok(InvocationPolicy::Fifo),
        "Priority" | "priority" => Ok(InvocationPolicy::Priority),
        "Pattern" | "pattern" => Ok(InvocationPolicy::Pattern),
        "AgeWeighted" | "age_weighted" => Ok(InvocationPolicy::AgeWeighted),
        // Domain-specific TOMLs use a wider vocabulary than the four canonical
        // values. Each spelling below maps onto the closest canonical value, so
        // policy reads succeed for those configurations. The mapping is part of
        // the executable configuration parser.
        "Continuous"
        | "Message"
        | "UI_Event"
        | "UI_Or_Data_Event"
        | "Vsync"
        | "Time"
        | "Time_Or_DepCompletion"
        | "Demand_Pull"
        | "Dependency_Completion"
        | "Dep_Completion"
        | "Programmatic"
        | "Synchronous"
        | "Manual"
        | "BlockingRead"
        | "Blocking_Read"
        | "SynchronousHandshake"
        | "Name_Passing"
        | "NamePassing"
        | "Per_Tick" => Ok(InvocationPolicy::Fifo),
        other => Err(format!("unknown invocation policy: {}", other)),
    }
}

fn parse_topology(s: &str) -> Result<TopologyPolicy, String> {
    match s {
        "DeclaredStatic"
        | "declared_static"
        | "Declared"
        | "Declared_DAG"
        | "Declared_DAG_Task"
        | "Declared_Observable_Chain"
        | "Per_Tick_Declared"
        | "Declared_On_Actors"
        | "Star" => Ok(TopologyPolicy::DeclaredStatic),
        "DeclaredMutable"
        | "declared_mutable"
        | "Declared_Mutable"
        | "Constructed"
        | "Declared/Dynamic"
        | "Declared_Or_Dynamic" => Ok(TopologyPolicy::DeclaredMutable),
        "RuntimeAddressable"
        | "runtime_addressable"
        | "Runtime_Addressable"
        | "Dynamic_Addressable"
        | "Runtime-emergent"
        | "RuntimeEmergent" => Ok(TopologyPolicy::RuntimeAddressable),
        "RuntimeAnonymous" | "runtime_anonymous" | "None" | "none" => {
            Ok(TopologyPolicy::RuntimeAnonymous)
        }
        other => Err(format!("unknown topology policy: {}", other)),
    }
}

fn parse_dependency(s: &str) -> Result<DependencyPolicy, String> {
    match s {
        "Fixed" | "fixed" => Ok(DependencyPolicy::Fixed),
        "HotSwappable" | "hot_swappable" | "Hot_Swappable" => Ok(DependencyPolicy::HotSwappable),
        "Conditional" | "conditional" | "ContentHash" | "Content_Hash" => {
            Ok(DependencyPolicy::Conditional)
        }
        other => Err(format!("unknown dependency policy: {}", other)),
    }
}

fn parse_lifecycle(s: &str) -> Result<LifecyclePolicy, String> {
    match s {
        "Simple" | "simple" | "None" => Ok(LifecyclePolicy::Simple),
        "Supervision" | "supervision" | "Supervised" => Ok(LifecyclePolicy::Supervision),
        // Continuation-as-new is the temporal continuation lifecycle.
        "Continuation" | "Continuation_As_New" => Ok(LifecyclePolicy::Continuation),
        "Checkpoint"
        | "checkpoint"
        | "Continuous"
        | "Rerun"
        | "Rerun_From_Failure"
        | "Rerun_On_Change"
        | "Retry"
        | "Sync_Barrier"
        | "Barrier"
        | "Per_Tick"
        | "Per_Frame"
        | "Per_Invocation"
        | "Subscription"
        | "Stateful"
        | "Reference_Tracked"
        | "Managed"
        | "Content_Hash_Incremental" => Ok(LifecyclePolicy::Checkpoint),
        "Drain" | "drain" => Ok(LifecyclePolicy::Drain),
        other => Err(format!("unknown lifecycle policy: {}", other)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::workloads::{Operator, OperatorFactory};
    use std::collections::HashMap;

    // -------------------- SingleModalityMock --------------------
    //
    // Compatible only with Sequential. trace_properties returns one
    // non-trivial predicate (`!out.is_empty()`). Dispatcher must
    // route through the trace_properties path (not the tautological
    // self-comparison) and Pass.

    struct SingleModalityMock;

    struct CollectOp;
    impl Operator<i64> for CollectOp {
        fn on_record(&mut self, r: i64) -> Vec<i64> {
            vec![r]
        }
    }

    impl Workload for SingleModalityMock {
        type Record = i64;
        type Output = Vec<i64>;
        type OpId = &'static str;

        fn operators(&self) -> Vec<(&'static str, OperatorFactory<i64>)> {
            let f: OperatorFactory<i64> = Box::new(|| Box::new(CollectOp));
            vec![("only", f)]
        }
        fn edges(&self) -> Vec<(&'static str, &'static str)> {
            Vec::new()
        }
        fn initial_inputs(&self) -> HashMap<&'static str, Vec<i64>> {
            let mut m = HashMap::new();
            m.insert("only", vec![1, 2, 3]);
            m
        }
        fn reduce(&self, sinks: HashMap<&'static str, Vec<i64>>) -> Vec<i64> {
            sinks.into_iter().flat_map(|(_, v)| v).collect()
        }
        fn compatible_modalities(&self) -> &'static [Modality] {
            &[Modality::Sequential]
        }
        fn trace_properties(&self, _cv: &ConfigVector) -> Vec<Box<dyn Fn(&Vec<i64>) -> bool>> {
            // Non-trivial: output must be non-empty AND hold the exact records
            // declared as input. The exact-records check catches a driver that
            // drops or duplicates records.
            vec![
                Box::new(|out: &Vec<i64>| !out.is_empty()),
                Box::new(|out: &Vec<i64>| {
                    let mut s = out.clone();
                    s.sort();
                    s == vec![1, 2, 3]
                }),
            ]
        }
    }

    #[test]
    fn single_modality_routes_through_trace_properties() {
        let w = SingleModalityMock;
        let cv = ConfigVector::default_for_test();
        let outcome = run_workload(&w, Modality::Sequential, &cv);
        match outcome {
            HarnessOutcome::Pass(msg) => {
                assert!(
                    msg.contains("trace properties"),
                    "expected trace_properties path, got: {}",
                    msg
                );
            }
            HarnessOutcome::Fail(msg) => panic!("unexpected Fail: {}", msg),
        }
    }

    // -------------------- EmptyTracePropertiesMock --------------------
    //
    // Single-modality + empty trace_properties. Dispatcher MUST
    // return Fail rather than vacuous Pass.

    struct EmptyTracePropertiesMock;

    impl Workload for EmptyTracePropertiesMock {
        type Record = i64;
        type Output = Vec<i64>;
        type OpId = &'static str;

        fn operators(&self) -> Vec<(&'static str, OperatorFactory<i64>)> {
            let f: OperatorFactory<i64> = Box::new(|| Box::new(CollectOp));
            vec![("only", f)]
        }
        fn edges(&self) -> Vec<(&'static str, &'static str)> {
            Vec::new()
        }
        fn initial_inputs(&self) -> HashMap<&'static str, Vec<i64>> {
            let mut m = HashMap::new();
            m.insert("only", vec![1]);
            m
        }
        fn reduce(&self, sinks: HashMap<&'static str, Vec<i64>>) -> Vec<i64> {
            sinks.into_iter().flat_map(|(_, v)| v).collect()
        }
        fn compatible_modalities(&self) -> &'static [Modality] {
            &[Modality::Sequential]
        }
        // trace_properties intentionally not overridden -> default Vec::new()
    }

    #[test]
    fn empty_trace_properties_on_single_modality_fails() {
        let w = EmptyTracePropertiesMock;
        let cv = ConfigVector::default_for_test();
        let outcome = run_workload(&w, Modality::Sequential, &cv);
        match outcome {
            HarnessOutcome::Fail(msg) => {
                assert!(
                    msg.contains("trace_properties") || msg.contains("nothing to assert"),
                    "expected trace_properties failure, got: {}",
                    msg
                );
            }
            HarnessOutcome::Pass(msg) => {
                panic!("expected Fail (vacuous-pass guard), got Pass: {}", msg)
            }
        }
    }

    // -------------------- CrossModalityMock --------------------
    //
    // Compatible with Sequential + ForkJoin, in one equivalence
    // class. Operator state counts records; reduce returns the max.
    // Sequential's single instance sees all N records and emits N
    // at EOS; ForkJoin's K instances each see ~N/K and emit ~N/K;
    // max diverges. Dispatcher must detect the divergence and
    // return Fail.

    struct CrossModalityMock;

    struct CountOp {
        count: i64,
    }
    impl Operator<i64> for CountOp {
        fn on_record(&mut self, _r: i64) -> Vec<i64> {
            self.count += 1;
            Vec::new()
        }
        fn on_end_of_stream(&mut self) -> Vec<i64> {
            vec![self.count]
        }
    }

    impl Workload for CrossModalityMock {
        type Record = i64;
        type Output = i64;
        type OpId = &'static str;

        fn operators(&self) -> Vec<(&'static str, OperatorFactory<i64>)> {
            let f: OperatorFactory<i64> = Box::new(|| Box::new(CountOp { count: 0 }));
            vec![("only", f)]
        }
        fn edges(&self) -> Vec<(&'static str, &'static str)> {
            Vec::new()
        }
        fn initial_inputs(&self) -> HashMap<&'static str, Vec<i64>> {
            let mut m = HashMap::new();
            // 8 records, default fork-join workers = 4 -> 4 chunks of 2
            m.insert("only", (0..8).collect());
            m
        }
        fn reduce(&self, sinks: HashMap<&'static str, Vec<i64>>) -> i64 {
            sinks.into_iter().flat_map(|(_, v)| v).max().unwrap_or(0)
        }
        fn compatible_modalities(&self) -> &'static [Modality] {
            &[Modality::Sequential, Modality::ForkJoin]
        }
        fn equivalence_classes(&self) -> Vec<Vec<Modality>> {
            vec![vec![Modality::Sequential, Modality::ForkJoin]]
        }
    }

    #[test]
    fn cross_modality_comparison_detects_divergence() {
        let w = CrossModalityMock;
        let cv = ConfigVector::default_for_test();
        let outcome = run_workload(&w, Modality::ForkJoin, &cv);
        match outcome {
            HarnessOutcome::Fail(msg) => {
                assert!(
                    msg.contains("ForkJoin") && msg.contains("Sequential"),
                    "expected cross-modality mismatch, got: {}",
                    msg
                );
            }
            HarnessOutcome::Pass(msg) => {
                panic!("dispatcher missed cross-modality divergence: {}", msg)
            }
        }
    }
}
