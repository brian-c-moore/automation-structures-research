use crate::crdt_reference as references;

use formal_example_structures::{
    ActuationPass, RecipeEdge, Reduction, ResourceRegistry, Sequential, Structure, StructureError,
    TraceLog,
};
use std::collections::{BTreeMap, BTreeSet};

pub use references::{evaluate_issued_operations, singleton_view};

const RUN_SUBJECT: &str = "FEX-DOM-DIST-01::run";
const OPERATION_SUBJECT: &str = "FEX-DOM-DIST-01::operations";
const MESSAGE_SUBJECT: &str = "FEX-DOM-DIST-01::messages";

const DELIVERY_STRUCTURES: &[Structure] = &[
    Structure::Sequential,
    Structure::Reduction,
    Structure::ActuationPass,
];

const DELIVERY_EDGES: &[RecipeEdge] = &[
    RecipeEdge {
        before: Structure::Sequential,
        before_action: "Begin",
        after: Structure::Reduction,
        after_action: "Commit",
    },
    RecipeEdge {
        before: Structure::Reduction,
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

const EDIT_STRUCTURES: &[Structure] = &[
    Structure::Sequential,
    Structure::ResourceRegistry,
    Structure::ActuationPass,
];

const EDIT_EDGES: &[RecipeEdge] = &[
    RecipeEdge {
        before: Structure::Sequential,
        before_action: "Begin",
        after: Structure::ResourceRegistry,
        after_action: "Store",
    },
    RecipeEdge {
        before: Structure::ResourceRegistry,
        before_action: "Store",
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

const CAPTURE_STRUCTURES: &[Structure] = &[Structure::Sequential, Structure::ResourceRegistry];

const CAPTURE_EDGES: &[RecipeEdge] = &[
    RecipeEdge {
        before: Structure::Sequential,
        before_action: "Begin",
        after: Structure::ResourceRegistry,
        after_action: "Store",
    },
    RecipeEdge {
        before: Structure::ResourceRegistry,
        before_action: "Store",
        after: Structure::Sequential,
        after_action: "Complete",
    },
];

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum JsonScalar {
    Null,
    Bool(bool),
    Integer(i64),
    String(String),
}

impl From<&str> for JsonScalar {
    fn from(value: &str) -> Self {
        Self::String(value.to_string())
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct JsonPath(pub Vec<String>);

impl JsonPath {
    pub fn new(parts: impl IntoIterator<Item = impl Into<String>>) -> Result<Self, StructureError> {
        let parts = parts.into_iter().map(Into::into).collect::<Vec<_>>();
        if parts.is_empty() || parts.iter().any(String::is_empty) {
            return Err(StructureError::new(
                "JSON paths require one or more nonempty map keys",
            ));
        }
        Ok(Self(parts))
    }

    pub fn key(key: &str) -> Self {
        Self(vec![key.to_string()])
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Dot {
    pub replica: String,
    pub counter: u64,
}

impl Dot {
    fn registry_id(&self) -> String {
        format!("{}:{}", self.replica, self.counter)
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum OperationAction {
    Assign(JsonScalar),
    Delete,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Operation {
    pub id: Dot,
    pub dependencies: BTreeSet<Dot>,
    pub path: JsonPath,
    pub action: OperationAction,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ReplicaState {
    pub(crate) operations: BTreeMap<Dot, BTreeSet<Operation>>,
}

impl ReplicaState {
    pub fn operation_count(&self) -> usize {
        self.operations.values().map(BTreeSet::len).sum()
    }

    pub fn identities(&self) -> BTreeSet<Dot> {
        self.operations.keys().cloned().collect()
    }

    pub fn operations(&self) -> impl Iterator<Item = &Operation> {
        self.operations.values().flat_map(BTreeSet::iter)
    }

    fn insert(&mut self, operation: Operation) {
        self.operations
            .entry(operation.id.clone())
            .or_default()
            .insert(operation);
    }

    fn join_union(&self, other: &Self) -> Self {
        let mut merged = self.clone();
        for (identity, operations) in &other.operations {
            merged
                .operations
                .entry(identity.clone())
                .or_default()
                .extend(operations.iter().cloned());
        }
        merged
    }

    fn is_subset_of(&self, other: &Self) -> bool {
        self.operations.iter().all(|(identity, operations)| {
            other
                .operations
                .get(identity)
                .is_some_and(|other_operations| operations.is_subset(other_operations))
        })
    }

    fn remove_identity(&mut self, identity: &Dot) {
        self.operations.remove(identity);
    }
}

pub type DocumentView = BTreeMap<JsonPath, BTreeSet<JsonScalar>>;

#[derive(Clone, Debug, Eq, PartialEq)]
struct Replica {
    id: String,
    next_counter: u64,
    state: ReplicaState,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ScriptStep {
    Assign {
        replica: String,
        path: JsonPath,
        value: JsonScalar,
    },
    Delete {
        replica: String,
        path: JsonPath,
    },
    Capture {
        replica: String,
        message: String,
    },
    Deliver {
        message: String,
        target: String,
    },
}

impl ScriptStep {
    pub fn assign(replica: &str, path: JsonPath, value: impl Into<JsonScalar>) -> Self {
        Self::Assign {
            replica: replica.to_string(),
            path,
            value: value.into(),
        }
    }

    pub fn delete(replica: &str, path: JsonPath) -> Self {
        Self::Delete {
            replica: replica.to_string(),
            path,
        }
    }

    pub fn capture(replica: &str, message: &str) -> Self {
        Self::Capture {
            replica: replica.to_string(),
            message: message.to_string(),
        }
    }

    pub fn deliver(message: &str, target: &str) -> Self {
        Self::Deliver {
            message: message.to_string(),
            target: target.to_string(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CrdtControl {
    Honest,
    ReuseOperationIdentity,
    BypassReduction,
    LeftBiasedMerge,
    DuplicateAsFresh,
    DropCausalContext,
    LoseConcurrentValue,
    DropDelete,
    MisdirectDelivery,
    IncompleteConvergence,
    MisorderLaterDelivery,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MergeMode {
    Union,
    LeftBiased,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum QueryMode {
    MultiValue,
    LastWriterWins,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EditWitness {
    pub subject: String,
    pub target: String,
    pub before: ReplicaState,
    pub operation: Operation,
    pub after: ReplicaState,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeliveryWitness {
    pub subject: String,
    pub message: String,
    pub named_target: String,
    pub actual_target: String,
    pub target_before: ReplicaState,
    pub captured_payload: ReplicaState,
    pub delivered_payload: ReplicaState,
    pub merged: ReplicaState,
    pub used_reduction: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CaptureWitness {
    pub subject: String,
    pub message: String,
    pub payload: ReplicaState,
}

pub struct CrdtRun {
    replica_registry: ResourceRegistry<usize>,
    operation_registry: ResourceRegistry<Operation>,
    message_registry: ResourceRegistry<ReplicaState>,
    issued_ids: Vec<String>,
    pub issued_operations: Vec<Operation>,
    pub replicas: BTreeMap<String, ReplicaState>,
    pub edit_witnesses: Vec<EditWitness>,
    pub capture_witnesses: Vec<CaptureWitness>,
    pub delivery_witnesses: Vec<DeliveryWitness>,
    pub observed_views: BTreeMap<String, DocumentView>,
    pub trace: TraceLog,
    merge_mode: MergeMode,
}

impl CrdtRun {
    pub fn view(&self, replica: &str) -> Option<&DocumentView> {
        self.observed_views.get(replica)
    }
}

pub fn run_script(
    replica_ids: &[&str],
    steps: &[ScriptStep],
    control: CrdtControl,
) -> Result<CrdtRun, StructureError> {
    if replica_ids.len() < 2 {
        return Err(StructureError::new(
            "FEX-DOM-DIST-01 requires at least two replicas",
        ));
    }
    if steps.is_empty() {
        return Err(StructureError::new(
            "FEX-DOM-DIST-01 requires a nonempty script",
        ));
    }

    let mut trace = TraceLog::default();
    let replica_registry = ResourceRegistry::build(
        replica_ids
            .iter()
            .enumerate()
            .map(|(index, id)| ((*id).to_string(), index)),
        &mut trace,
        RUN_SUBJECT,
    )?;
    let mut operation_registry = ResourceRegistry::empty(&mut trace, OPERATION_SUBJECT);
    let mut issued_ids = Vec::new();
    let mut issued_operations = Vec::new();
    let mut replicas = replica_ids
        .iter()
        .map(|id| Replica {
            id: (*id).to_string(),
            next_counter: 0,
            state: ReplicaState::default(),
        })
        .collect::<Vec<_>>();
    let replica_indexes = replica_ids
        .iter()
        .enumerate()
        .map(|(index, id)| ((*id).to_string(), index))
        .collect::<BTreeMap<_, _>>();
    let mut message_registry = ResourceRegistry::empty(&mut trace, MESSAGE_SUBJECT);
    let mut edit_witnesses = Vec::new();
    let mut capture_witnesses = Vec::new();
    let mut delivery_witnesses = Vec::new();
    let mut carrier = Sequential::new(
        steps.len() as u64,
        "initialized".to_string(),
        &mut trace,
        RUN_SUBJECT,
    )?;
    let merge_mode = if control == CrdtControl::LeftBiasedMerge {
        MergeMode::LeftBiased
    } else {
        MergeMode::Union
    };
    let mut delivery_number = 0usize;

    for (index, action) in steps.iter().enumerate() {
        let subject = format!("FEX-DOM-DIST-01::step-{index}");
        let step = carrier.begin_step(&mut trace, &subject)?;
        let description = match action {
            ScriptStep::Assign {
                replica,
                path,
                value,
            } => {
                apply_edit(
                    &mut replicas,
                    &replica_indexes,
                    &mut operation_registry,
                    &mut issued_ids,
                    &mut issued_operations,
                    replica,
                    path.clone(),
                    OperationAction::Assign(value.clone()),
                    control,
                    &mut trace,
                    &subject,
                    &mut edit_witnesses,
                )?;
                format!("assign:{replica}")
            }
            ScriptStep::Delete { replica, path } => {
                apply_edit(
                    &mut replicas,
                    &replica_indexes,
                    &mut operation_registry,
                    &mut issued_ids,
                    &mut issued_operations,
                    replica,
                    path.clone(),
                    OperationAction::Delete,
                    control,
                    &mut trace,
                    &subject,
                    &mut edit_witnesses,
                )?;
                format!("delete:{replica}")
            }
            ScriptStep::Capture { replica, message } => {
                let replica_index = resolve_replica(&replica_indexes, replica)?;
                message_registry.insert(
                    message.clone(),
                    replicas[replica_index].state.clone(),
                    &mut trace,
                    &subject,
                )?;
                capture_witnesses.push(CaptureWitness {
                    subject: subject.clone(),
                    message: message.clone(),
                    payload: replicas[replica_index].state.clone(),
                });
                format!("capture:{replica}:{message}")
            }
            ScriptStep::Deliver { message, target } => {
                let captured = message_registry.get(message).cloned().ok_or_else(|| {
                    StructureError::new(format!("unknown captured message {message}"))
                })?;
                apply_delivery(
                    &mut replicas,
                    &replica_indexes,
                    message,
                    target,
                    captured,
                    control,
                    delivery_number,
                    merge_mode,
                    &mut trace,
                    &subject,
                    &mut delivery_witnesses,
                )?;
                delivery_number += 1;
                format!("deliver:{message}:{target}")
            }
        };
        carrier.complete_step(step, description, &mut trace, &subject)?;
    }
    carrier.done_stuttering(&mut trace, RUN_SUBJECT)?;

    if control == CrdtControl::IncompleteConvergence {
        if let Some(identity) = issued_operations
            .first()
            .map(|operation| operation.id.clone())
        {
            for replica in &mut replicas {
                replica.state.remove_identity(&identity);
            }
        }
    }

    let query_mode = if control == CrdtControl::LoseConcurrentValue {
        QueryMode::LastWriterWins
    } else {
        QueryMode::MultiValue
    };
    let replica_states = replicas
        .iter()
        .map(|replica| (replica.id.clone(), replica.state.clone()))
        .collect::<BTreeMap<_, _>>();
    let observed_views = replicas
        .iter()
        .map(|replica| {
            materialize_state(&replica.state, query_mode).map(|view| (replica.id.clone(), view))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()?;

    Ok(CrdtRun {
        replica_registry,
        operation_registry,
        message_registry,
        issued_ids,
        issued_operations,
        replicas: replica_states,
        edit_witnesses,
        capture_witnesses,
        delivery_witnesses,
        observed_views,
        trace,
        merge_mode,
    })
}

#[allow(clippy::too_many_arguments)]
fn apply_edit(
    replicas: &mut [Replica],
    replica_indexes: &BTreeMap<String, usize>,
    operation_registry: &mut ResourceRegistry<Operation>,
    issued_ids: &mut Vec<String>,
    issued_operations: &mut Vec<Operation>,
    replica_id: &str,
    path: JsonPath,
    action: OperationAction,
    control: CrdtControl,
    trace: &mut TraceLog,
    subject: &str,
    witnesses: &mut Vec<EditWitness>,
) -> Result<(), StructureError> {
    let replica_index = resolve_replica(replica_indexes, replica_id)?;
    let before = replicas[replica_index].state.clone();
    let next_counter = replicas[replica_index]
        .next_counter
        .checked_add(1)
        .ok_or_else(|| StructureError::new("operation counter overflow"))?;
    let identity = if control == CrdtControl::ReuseOperationIdentity {
        issued_operations
            .first()
            .map(|operation| operation.id.clone())
            .unwrap_or_else(|| Dot {
                replica: replica_id.to_string(),
                counter: next_counter,
            })
    } else {
        Dot {
            replica: replica_id.to_string(),
            counter: next_counter,
        }
    };
    let dependencies = if control == CrdtControl::DropCausalContext && !before.operations.is_empty()
    {
        BTreeSet::new()
    } else {
        before.identities()
    };
    let operation = Operation {
        id: identity,
        dependencies,
        path,
        action,
    };

    let registry_id = operation.id.registry_id();
    operation_registry.insert(registry_id.clone(), operation.clone(), trace, subject)?;
    issued_ids.push(registry_id);
    issued_operations.push(operation.clone());
    replicas[replica_index].next_counter = next_counter;

    let mut pass = ActuationPass::new(vec![Some(replica_index)], trace, subject);
    pass.actuate_with(
        0,
        replicas,
        |replica, _, _| {
            replica.state.insert(operation.clone());
            Ok(())
        },
        trace,
        subject,
    )?;
    pass.finish(trace, subject)?;
    witnesses.push(EditWitness {
        subject: subject.to_string(),
        target: replica_id.to_string(),
        before,
        operation,
        after: replicas[replica_index].state.clone(),
    });
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn apply_delivery(
    replicas: &mut [Replica],
    replica_indexes: &BTreeMap<String, usize>,
    message: &str,
    target: &str,
    captured_payload: ReplicaState,
    control: CrdtControl,
    delivery_number: usize,
    merge_mode: MergeMode,
    trace: &mut TraceLog,
    subject: &str,
    witnesses: &mut Vec<DeliveryWitness>,
) -> Result<(), StructureError> {
    let named_target_index = resolve_replica(replica_indexes, target)?;
    let actual_target_index = if control == CrdtControl::MisdirectDelivery {
        (named_target_index + 1) % replicas.len()
    } else {
        named_target_index
    };
    let actual_target = replicas[actual_target_index].id.clone();
    let target_before = replicas[actual_target_index].state.clone();
    let delivered_payload = mutate_delivery_payload(&captured_payload, control);
    let bypass_reduction = control == CrdtControl::BypassReduction;
    let misorder = control == CrdtControl::MisorderLaterDelivery && delivery_number > 0;

    let merged = if bypass_reduction || misorder {
        merge_states(&target_before, &delivered_payload, merge_mode)
    } else {
        reduce_payloads(
            [delivered_payload.clone()],
            target_before.clone(),
            merge_mode,
            trace,
            subject,
        )
    };

    let mut pass = ActuationPass::new(vec![Some(actual_target_index)], trace, subject);
    pass.actuate_with(
        0,
        replicas,
        |replica, _, _| {
            replica.state = merged.clone();
            Ok(())
        },
        trace,
        subject,
    )?;
    pass.finish(trace, subject)?;

    if misorder {
        let _ = reduce_payloads(
            [delivered_payload.clone()],
            target_before.clone(),
            merge_mode,
            trace,
            subject,
        );
    }

    witnesses.push(DeliveryWitness {
        subject: subject.to_string(),
        message: message.to_string(),
        named_target: target.to_string(),
        actual_target,
        target_before,
        captured_payload,
        delivered_payload,
        merged,
        used_reduction: !bypass_reduction,
    });
    Ok(())
}

fn mutate_delivery_payload(payload: &ReplicaState, control: CrdtControl) -> ReplicaState {
    match control {
        CrdtControl::DuplicateAsFresh => {
            let mut mutated = payload.clone();
            for operation in payload.operations() {
                let mut duplicate = operation.clone();
                duplicate.id.replica.push_str("#duplicate");
                mutated.insert(duplicate);
            }
            mutated
        }
        CrdtControl::DropDelete => {
            let mut mutated = ReplicaState::default();
            for operation in payload.operations() {
                if operation.action != OperationAction::Delete {
                    mutated.insert(operation.clone());
                }
            }
            mutated
        }
        _ => payload.clone(),
    }
}

fn resolve_replica(
    replica_indexes: &BTreeMap<String, usize>,
    replica: &str,
) -> Result<usize, StructureError> {
    replica_indexes
        .get(replica)
        .copied()
        .ok_or_else(|| StructureError::new(format!("unknown replica {replica}")))
}

fn merge_states(left: &ReplicaState, right: &ReplicaState, mode: MergeMode) -> ReplicaState {
    match mode {
        MergeMode::Union => left.join_union(right),
        MergeMode::LeftBiased => left.clone(),
    }
}

fn reduce_payloads(
    candidates: impl IntoIterator<Item = ReplicaState>,
    identity: ReplicaState,
    mode: MergeMode,
    trace: &mut TraceLog,
    subject: &str,
) -> ReplicaState {
    Reduction::fold(
        candidates,
        identity,
        |left, right| merge_states(&left, &right, mode),
        trace,
        subject,
    )
}

fn materialize_state(
    state: &ReplicaState,
    mode: QueryMode,
) -> Result<DocumentView, StructureError> {
    for (identity, operations) in &state.operations {
        if operations.len() != 1 {
            return Err(StructureError::new(format!(
                "operation identity {}:{} has {} bodies",
                identity.replica,
                identity.counter,
                operations.len()
            )));
        }
    }

    let operations = state.operations().collect::<Vec<_>>();
    let mut dominated = BTreeSet::new();
    for later in &operations {
        for earlier in &operations {
            if later.path == earlier.path && later.dependencies.contains(&earlier.id) {
                dominated.insert(earlier.id.clone());
            }
        }
    }

    let mut view = DocumentView::new();
    for operation in operations {
        if dominated.contains(&operation.id) {
            continue;
        }
        if let OperationAction::Assign(value) = &operation.action {
            view.entry(operation.path.clone())
                .or_default()
                .insert(value.clone());
        }
    }
    if mode == QueryMode::LastWriterWins {
        for values in view.values_mut() {
            if let Some(last) = values.iter().next_back().cloned() {
                values.clear();
                values.insert(last);
            }
        }
    }
    Ok(view)
}

pub fn verify_run(run: &CrdtRun) -> Result<(), StructureError> {
    if run.replica_registry.len() != run.replicas.len() {
        return Err(StructureError::new(
            "replica registry differs from the executed replica set",
        ));
    }
    for replica in run.replicas.keys() {
        if !run.replica_registry.contains(replica) {
            return Err(StructureError::new(format!(
                "executed replica {replica} is absent from the replica registry"
            )));
        }
    }
    if run.operation_registry.len() != run.issued_operations.len()
        || run.issued_ids.len() != run.issued_operations.len()
    {
        return Err(StructureError::new(
            "operation registry and issued-operation projection differ",
        ));
    }
    for (registry_id, operation) in run.issued_ids.iter().zip(&run.issued_operations) {
        if run.operation_registry.get(registry_id) != Some(operation) {
            return Err(StructureError::new(format!(
                "operation registry content differs for {registry_id}"
            )));
        }
    }

    for edit in &run.edit_witnesses {
        if edit.operation.dependencies != edit.before.identities() {
            return Err(StructureError::new(format!(
                "edit {} does not bind the complete visible causal context",
                edit.subject
            )));
        }
        let mut expected = edit.before.clone();
        expected.insert(edit.operation.clone());
        if edit.after != expected || !edit.before.is_subset_of(&edit.after) {
            return Err(StructureError::new(format!(
                "edit {} is not a monotone single-operation update",
                edit.subject
            )));
        }
        run.trace
            .verify_recipe_instance_for(&edit.subject, EDIT_STRUCTURES, EDIT_EDGES)?;
    }

    for capture in &run.capture_witnesses {
        if run.message_registry.get(&capture.message) != Some(&capture.payload) {
            return Err(StructureError::new(format!(
                "capture {} differs from its registered message payload",
                capture.subject
            )));
        }
        run.trace.verify_recipe_instance_for(
            &capture.subject,
            CAPTURE_STRUCTURES,
            CAPTURE_EDGES,
        )?;
    }

    for delivery in &run.delivery_witnesses {
        if run.message_registry.get(&delivery.message) != Some(&delivery.captured_payload) {
            return Err(StructureError::new(format!(
                "delivery {} differs from its registered captured message",
                delivery.subject
            )));
        }
        if delivery.named_target != delivery.actual_target {
            return Err(StructureError::new(format!(
                "delivery {} changed {} instead of {}",
                delivery.subject, delivery.actual_target, delivery.named_target
            )));
        }
        if delivery.captured_payload != delivery.delivered_payload {
            return Err(StructureError::new(format!(
                "delivery {} changed the captured message payload",
                delivery.subject
            )));
        }
        let expected =
            references::reconstruct_lub_union(&delivery.target_before, &delivery.delivered_payload);
        if delivery.merged != expected
            || !delivery.target_before.is_subset_of(&delivery.merged)
            || !delivery.delivered_payload.is_subset_of(&delivery.merged)
        {
            return Err(StructureError::new(format!(
                "delivery {} did not commit the exact upper-bound state",
                delivery.subject
            )));
        }
        if !delivery.used_reduction {
            return Err(StructureError::new(format!(
                "delivery {} bypassed Reduction",
                delivery.subject
            )));
        }
        run.trace.verify_recipe_instance_for(
            &delivery.subject,
            DELIVERY_STRUCTURES,
            DELIVERY_EDGES,
        )?;
    }

    let mut candidate_states = vec![ReplicaState::default()];
    for edit in &run.edit_witnesses {
        candidate_states.push(edit.before.clone());
        candidate_states.push(edit.after.clone());
    }
    for delivery in &run.delivery_witnesses {
        candidate_states.push(delivery.target_before.clone());
        candidate_states.push(delivery.delivered_payload.clone());
        candidate_states.push(delivery.merged.clone());
    }
    candidate_states.extend(run.replicas.values().cloned());
    verify_merge_laws(&candidate_states, run.merge_mode)?;

    let issued_reference = references::exact_issued_state(&run.issued_operations);
    let expected_state = ReplicaState {
        operations: issued_reference,
    };
    let expected_view =
        evaluate_issued_operations(&run.issued_operations).map_err(StructureError::new)?;
    for (replica, state) in &run.replicas {
        if state != &expected_state {
            return Err(StructureError::new(format!(
                "replica {replica} does not contain the complete issued operation set"
            )));
        }
        if run.observed_views.get(replica) != Some(&expected_view) {
            return Err(StructureError::new(format!(
                "replica {replica} materialized a view that differs from the separate evaluator"
            )));
        }
    }
    run.trace
        .require_single_event_for(Structure::Sequential, "Done", RUN_SUBJECT)?;
    Ok(())
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct LawCounts {
    pub idempotence: usize,
    pub commutativity: usize,
    pub associativity: usize,
}

fn verify_merge_laws(
    states: &[ReplicaState],
    mode: MergeMode,
) -> Result<LawCounts, StructureError> {
    let mut counts = LawCounts::default();
    for left in states {
        counts.idempotence += 1;
        if merge_states(left, left, mode) != *left {
            return Err(StructureError::new("merge is not idempotent"));
        }
        for right in states {
            counts.commutativity += 1;
            if merge_states(left, right, mode) != merge_states(right, left, mode) {
                return Err(StructureError::new("merge is not commutative"));
            }
            for third in states {
                counts.associativity += 1;
                let left_grouped = merge_states(&merge_states(left, right, mode), third, mode);
                let right_grouped = merge_states(left, &merge_states(right, third, mode), mode);
                if left_grouped != right_grouped {
                    return Err(StructureError::new("merge is not associative"));
                }
            }
        }
    }
    Ok(counts)
}

pub fn published_concurrent_assignment_script(
    left: impl Into<JsonScalar>,
    right: impl Into<JsonScalar>,
) -> Vec<ScriptStep> {
    let key = JsonPath::key("key");
    vec![
        ScriptStep::assign("p", key.clone(), "A"),
        ScriptStep::capture("p", "initial"),
        ScriptStep::deliver("initial", "q"),
        ScriptStep::assign("p", key.clone(), left),
        ScriptStep::assign("q", key, right),
        ScriptStep::capture("p", "p-offline"),
        ScriptStep::capture("q", "q-offline"),
        ScriptStep::deliver("q-offline", "p"),
        ScriptStep::deliver("p-offline", "q"),
    ]
}

pub fn offline_different_paths_script() -> Vec<ScriptStep> {
    vec![
        ScriptStep::assign("p", JsonPath::key("title"), "draft"),
        ScriptStep::assign("q", JsonPath::new(["metadata", "reviewer"]).unwrap(), "sam"),
        ScriptStep::capture("p", "p-state"),
        ScriptStep::capture("q", "q-state"),
        ScriptStep::deliver("q-state", "p"),
        ScriptStep::deliver("p-state", "q"),
    ]
}

pub fn observed_overwrite_script() -> Vec<ScriptStep> {
    let key = JsonPath::key("key");
    vec![
        ScriptStep::assign("p", key.clone(), "old"),
        ScriptStep::assign("p", key, "new"),
        ScriptStep::capture("p", "latest"),
        ScriptStep::deliver("latest", "q"),
    ]
}

pub fn observed_delete_with_stale_delivery_script() -> Vec<ScriptStep> {
    let key = JsonPath::key("key");
    vec![
        ScriptStep::assign("p", key.clone(), "old"),
        ScriptStep::capture("p", "stale"),
        ScriptStep::deliver("stale", "q"),
        ScriptStep::delete("p", key),
        ScriptStep::capture("p", "deleted"),
        ScriptStep::deliver("deleted", "q"),
        ScriptStep::deliver("stale", "q"),
    ]
}

pub fn concurrent_delete_assign_script() -> Vec<ScriptStep> {
    let key = JsonPath::key("key");
    vec![
        ScriptStep::assign("p", key.clone(), "old"),
        ScriptStep::capture("p", "initial"),
        ScriptStep::deliver("initial", "q"),
        ScriptStep::delete("p", key.clone()),
        ScriptStep::assign("q", key, "new"),
        ScriptStep::capture("p", "p-delete"),
        ScriptStep::capture("q", "q-assign"),
        ScriptStep::deliver("q-assign", "p"),
        ScriptStep::deliver("p-delete", "q"),
    ]
}

pub fn expected_control_rejection(control: CrdtControl) -> Option<&'static str> {
    match control {
        CrdtControl::Honest => None,
        CrdtControl::ReuseOperationIdentity => Some("cannot replace existing ID"),
        CrdtControl::BypassReduction => Some("bypassed Reduction"),
        CrdtControl::LeftBiasedMerge => Some("did not commit the exact upper-bound state"),
        CrdtControl::DuplicateAsFresh | CrdtControl::DropDelete => {
            Some("changed the captured message payload")
        }
        CrdtControl::DropCausalContext => Some("does not bind the complete visible causal context"),
        CrdtControl::LoseConcurrentValue => {
            Some("materialized a view that differs from the separate evaluator")
        }
        CrdtControl::MisdirectDelivery => Some("changed p instead of q"),
        CrdtControl::IncompleteConvergence => {
            Some("does not contain the complete issued operation set")
        }
        CrdtControl::MisorderLaterDelivery => {
            Some("recipe edge Reduction.Commit -> ActuationPass.Commit is not ordered")
        }
    }
}

pub fn control_is_detected(control: CrdtControl) -> bool {
    let Some(expected) = expected_control_rejection(control) else {
        return false;
    };
    let script = match control {
        CrdtControl::DropCausalContext => observed_overwrite_script(),
        CrdtControl::DropDelete => observed_delete_with_stale_delivery_script(),
        _ => published_concurrent_assignment_script("B", "C"),
    };
    let observed = match run_script(&["p", "q"], &script, control) {
        Err(error) => error.to_string(),
        Ok(run) => match verify_run(&run) {
            Err(error) => error.to_string(),
            Ok(()) => return false,
        },
    };
    observed.contains(expected)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_positive(script: &[ScriptStep]) -> CrdtRun {
        run_positive_for(&["p", "q"], script)
    }

    fn run_positive_for(replica_ids: &[&str], script: &[ScriptStep]) -> CrdtRun {
        let run = run_script(replica_ids, script, CrdtControl::Honest).unwrap();
        verify_run(&run).unwrap();
        run
    }

    #[test]
    fn published_concurrent_assignment_retains_both_values() {
        let run = run_positive(&published_concurrent_assignment_script("B", "C"));
        let expected = singleton_view(JsonPath::key("key"), ["B".into(), "C".into()]);
        assert_eq!(run.view("p"), Some(&expected));
        assert_eq!(run.view("q"), Some(&expected));
    }

    #[test]
    fn offline_different_paths_converge() {
        let run = run_positive(&offline_different_paths_script());
        assert_eq!(run.view("p"), run.view("q"));
        assert_eq!(run.view("p").unwrap().len(), 2);
    }

    #[test]
    fn observed_overwrite_hides_the_earlier_value() {
        let run = run_positive(&observed_overwrite_script());
        let expected = singleton_view(JsonPath::key("key"), ["new".into()]);
        assert_eq!(run.view("p"), Some(&expected));
        assert_eq!(run.view("q"), Some(&expected));
    }

    #[test]
    fn observed_delete_does_not_resurrect_after_stale_delivery() {
        let run = run_positive(&observed_delete_with_stale_delivery_script());
        assert_eq!(run.view("p"), Some(&DocumentView::new()));
        assert_eq!(run.view("q"), Some(&DocumentView::new()));
    }

    #[test]
    fn concurrent_assignment_survives_an_observed_delete() {
        let run = run_positive(&concurrent_delete_assign_script());
        let expected = singleton_view(JsonPath::key("key"), ["new".into()]);
        assert_eq!(run.view("p"), Some(&expected));
        assert_eq!(run.view("q"), Some(&expected));
    }

    #[test]
    fn generated_concurrent_assignments_match_the_separate_evaluator() {
        let values = ["A", "B", "C", "D", "E", "F", "G", "H"];
        let mut comparisons = 0usize;
        for left in values {
            for right in values {
                let run = run_positive(&published_concurrent_assignment_script(left, right));
                let expected = evaluate_issued_operations(&run.issued_operations).unwrap();
                assert_eq!(run.view("p"), Some(&expected));
                comparisons += 1;
            }
        }
        assert_eq!(comparisons, 64);
    }

    #[test]
    fn generated_paths_edits_and_delivery_orders_match_the_separate_evaluator() {
        let paths = [
            JsonPath::key("key"),
            JsonPath::new(["metadata", "reviewer"]).unwrap(),
        ];
        let mut comparisons = 0usize;

        for path in paths {
            for delete_left in [false, true] {
                for reverse_delivery in [false, true] {
                    let mut script = vec![
                        ScriptStep::assign("p", path.clone(), "old"),
                        ScriptStep::capture("p", "initial"),
                        ScriptStep::deliver("initial", "q"),
                    ];
                    if delete_left {
                        script.push(ScriptStep::delete("p", path.clone()));
                    } else {
                        script.push(ScriptStep::assign("p", path.clone(), "P"));
                    }
                    script.extend([
                        ScriptStep::assign("q", path.clone(), "Q"),
                        ScriptStep::capture("p", "p-offline"),
                        ScriptStep::capture("q", "q-offline"),
                    ]);
                    let deliveries = if reverse_delivery {
                        [("p-offline", "q"), ("q-offline", "p")]
                    } else {
                        [("q-offline", "p"), ("p-offline", "q")]
                    };
                    for (message, target) in deliveries {
                        script.push(ScriptStep::deliver(message, target));
                    }

                    let run = run_positive(&script);
                    let expected = evaluate_issued_operations(&run.issued_operations).unwrap();
                    assert_eq!(run.view("p"), Some(&expected));
                    assert_eq!(run.view("q"), Some(&expected));
                    comparisons += 1;
                }
            }
        }
        assert_eq!(comparisons, 8);
    }

    #[test]
    fn multi_input_reduction_commits_the_same_join_in_every_order() {
        let run = run_script(
            &["p", "q", "r"],
            &[
                ScriptStep::assign("p", JsonPath::key("key"), "P"),
                ScriptStep::assign("q", JsonPath::key("key"), "Q"),
                ScriptStep::assign("r", JsonPath::key("key"), "R"),
                ScriptStep::capture("p", "p-state"),
                ScriptStep::capture("q", "q-state"),
                ScriptStep::capture("r", "r-state"),
            ],
            CrdtControl::Honest,
        )
        .unwrap();
        let payloads = ["p-state", "q-state", "r-state"]
            .map(|message| run.message_registry.get(message).cloned().unwrap());
        assert!(run
            .issued_operations
            .iter()
            .all(|operation| operation.dependencies.is_empty()));

        let pair_orders = [[0usize, 1usize], [1, 0]];
        let expected_pair = references::reconstruct_lub_union(&payloads[0], &payloads[1]);
        for (index, order) in pair_orders.into_iter().enumerate() {
            let subject = format!("FEX-DOM-DIST-01::batch-pair-{index}");
            let mut trace = TraceLog::default();
            let result = reduce_payloads(
                order.map(|payload| payloads[payload].clone()),
                ReplicaState::default(),
                MergeMode::Union,
                &mut trace,
                &subject,
            );
            assert_eq!(result, expected_pair);
            let event = trace
                .require_single_event_for(Structure::Reduction, "Evaluate", &subject)
                .unwrap();
            assert_eq!(event.detail, "candidates=2");
            trace
                .require_single_event_for(Structure::Reduction, "Commit", &subject)
                .unwrap();
        }

        let triple_orders = [
            [0usize, 1usize, 2usize],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ];
        let expected_triple = references::reconstruct_lub_union(&expected_pair, &payloads[2]);
        for (index, order) in triple_orders.into_iter().enumerate() {
            let subject = format!("FEX-DOM-DIST-01::batch-triple-{index}");
            let mut trace = TraceLog::default();
            let result = reduce_payloads(
                order.map(|payload| payloads[payload].clone()),
                ReplicaState::default(),
                MergeMode::Union,
                &mut trace,
                &subject,
            );
            assert_eq!(result, expected_triple);
            let event = trace
                .require_single_event_for(Structure::Reduction, "Evaluate", &subject)
                .unwrap();
            assert_eq!(event.detail, "candidates=3");
            trace
                .require_single_event_for(Structure::Reduction, "Commit", &subject)
                .unwrap();
        }
    }

    #[test]
    fn three_replica_delivery_permutations_and_duplicates_converge() {
        let permutations = [
            ["p-state", "q-state", "r-state"],
            ["p-state", "r-state", "q-state"],
            ["q-state", "p-state", "r-state"],
            ["q-state", "r-state", "p-state"],
            ["r-state", "p-state", "q-state"],
            ["r-state", "q-state", "p-state"],
        ];
        let expected = singleton_view(JsonPath::key("key"), ["P".into(), "Q".into(), "R".into()]);

        for permutation in permutations {
            let mut script = vec![
                ScriptStep::assign("p", JsonPath::key("key"), "P"),
                ScriptStep::assign("q", JsonPath::key("key"), "Q"),
                ScriptStep::assign("r", JsonPath::key("key"), "R"),
                ScriptStep::capture("p", "p-state"),
                ScriptStep::capture("q", "q-state"),
                ScriptStep::capture("r", "r-state"),
            ];
            for message in permutation {
                for target in ["p", "q", "r"] {
                    script.push(ScriptStep::deliver(message, target));
                }
            }
            for target in ["p", "q", "r"] {
                script.push(ScriptStep::deliver(permutation[0], target));
            }

            let run = run_positive_for(&["p", "q", "r"], &script);
            for replica in ["p", "q", "r"] {
                assert_eq!(run.view(replica), Some(&expected));
            }
        }
    }

    #[test]
    fn bounded_state_family_satisfies_the_merge_laws() {
        let run = run_positive(&published_concurrent_assignment_script("B", "C"));
        let issued = run.issued_operations.clone();
        let mut states = Vec::new();
        for mask in 0usize..(1usize << issued.len()) {
            let mut state = ReplicaState::default();
            for (index, operation) in issued.iter().enumerate() {
                if mask & (1usize << index) != 0 {
                    state.insert(operation.clone());
                }
            }
            states.push(state);
        }
        let counts = verify_merge_laws(&states, MergeMode::Union).unwrap();
        assert_eq!(states.len(), 8);
        assert_eq!(counts.idempotence, 8);
        assert_eq!(counts.commutativity, 64);
        assert_eq!(counts.associativity, 512);
    }

    #[test]
    fn every_registered_control_is_discriminating() {
        let controls = [
            CrdtControl::ReuseOperationIdentity,
            CrdtControl::BypassReduction,
            CrdtControl::LeftBiasedMerge,
            CrdtControl::DuplicateAsFresh,
            CrdtControl::DropCausalContext,
            CrdtControl::LoseConcurrentValue,
            CrdtControl::DropDelete,
            CrdtControl::MisdirectDelivery,
            CrdtControl::IncompleteConvergence,
            CrdtControl::MisorderLaterDelivery,
        ];
        for control in controls {
            assert!(control_is_detected(control), "control escaped: {control:?}");
        }
    }

    #[test]
    fn convergence_alone_does_not_accept_lost_concurrent_input() {
        let run = run_script(
            &["p", "q"],
            &published_concurrent_assignment_script("B", "C"),
            CrdtControl::LoseConcurrentValue,
        )
        .unwrap();
        assert_eq!(run.view("p"), run.view("q"));
        assert!(verify_run(&run).is_err());
    }

    #[test]
    fn agreement_without_complete_delivery_is_rejected() {
        let run = run_script(
            &["p", "q"],
            &published_concurrent_assignment_script("B", "C"),
            CrdtControl::IncompleteConvergence,
        )
        .unwrap();
        assert_eq!(run.replicas.get("p"), run.replicas.get("q"));
        assert!(verify_run(&run).is_err());
    }
}
