use crate::stm_reference::{self, OpacityEvaluation};

use formal_example_structures::{
    ActuationPass, Edge, RelationshipGraph, ResourceRegistry, Sequential, Structure,
    StructureError, TraceLog,
};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicU64, Ordering};

const RUN_SUBJECT: &str = "FEX-DOM-TXN-01::run";
const GRAPH_SUBJECT: &str = "FEX-DOM-TXN-01::access-graph";
const CELL_SUBJECT: &str = "FEX-DOM-TXN-01::cells";
const TXN_SUBJECT: &str = "FEX-DOM-TXN-01::transactions";

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AccessMode {
    Read,
    Write,
    ReadWrite,
}

impl AccessMode {
    fn weight(self) -> u64 {
        match self {
            Self::Read => 1,
            Self::Write => 2,
            Self::ReadWrite => 3,
        }
    }

    fn permits_read(self) -> bool {
        matches!(self, Self::Read | Self::ReadWrite)
    }

    fn permits_write(self) -> bool {
        matches!(self, Self::Write | Self::ReadWrite)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CellSpec {
    pub id: String,
    pub initial: i64,
}

impl CellSpec {
    pub fn new(id: impl Into<String>, initial: i64) -> Self {
        Self {
            id: id.into(),
            initial,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TransactionSpec {
    pub id: String,
    pub accesses: Vec<(String, AccessMode)>,
}

impl TransactionSpec {
    pub fn new(
        id: impl Into<String>,
        accesses: impl IntoIterator<Item = (impl Into<String>, AccessMode)>,
    ) -> Self {
        Self {
            id: id.into(),
            accesses: accesses
                .into_iter()
                .map(|(cell, mode)| (cell.into(), mode))
                .collect(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StmStep {
    Begin {
        transaction: String,
    },
    Read {
        transaction: String,
        cell: String,
    },
    Write {
        transaction: String,
        cell: String,
        value: i64,
    },
    CommitBegin {
        transaction: String,
    },
    ApplyNext {
        transaction: String,
    },
    CommitFinish {
        transaction: String,
    },
}

impl StmStep {
    pub fn begin(transaction: &str) -> Self {
        Self::Begin {
            transaction: transaction.to_string(),
        }
    }

    pub fn read(transaction: &str, cell: &str) -> Self {
        Self::Read {
            transaction: transaction.to_string(),
            cell: cell.to_string(),
        }
    }

    pub fn write(transaction: &str, cell: &str, value: i64) -> Self {
        Self::Write {
            transaction: transaction.to_string(),
            cell: cell.to_string(),
            value,
        }
    }

    pub fn commit_begin(transaction: &str) -> Self {
        Self::CommitBegin {
            transaction: transaction.to_string(),
        }
    }

    pub fn apply_next(transaction: &str) -> Self {
        Self::ApplyNext {
            transaction: transaction.to_string(),
        }
    }

    pub fn commit_finish(transaction: &str) -> Self {
        Self::CommitFinish {
            transaction: transaction.to_string(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StmControl {
    Honest,
    ReuseTransactionIdentity,
    UndeclaredAccess,
    IgnoreEpochValidation,
    AllowConflictingCommit,
    OmitWriteTarget,
    MisdirectWrite,
    PublishBeforeAllWrites,
    PartialAbortAfterWrite,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TransactionStatus {
    Active,
    Committing,
    PreparedReadOnly,
    Committed,
    Aborted,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TxnOperation {
    Read {
        cell: String,
        value: i64,
        sequence: u64,
    },
    Write {
        cell: String,
        value: i64,
        sequence: u64,
    },
}

impl TxnOperation {
    pub fn sequence(&self) -> u64 {
        match self {
            Self::Read { sequence, .. } | Self::Write { sequence, .. } => *sequence,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TransactionRecord {
    pub id: String,
    pub begin_sequence: u64,
    pub end_sequence: Option<u64>,
    pub start_epoch: u64,
    pub status: TransactionStatus,
    pub operations: Vec<TxnOperation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReadResult {
    pub transaction: String,
    pub cell: String,
    pub value: i64,
    pub sequence: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EpochAction {
    Acquire,
    Publish,
    ValidateReadOnly,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EpochEvent {
    pub transaction: String,
    pub action: EpochAction,
    pub before: u64,
    pub after: u64,
    pub sequence: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AppliedWrite {
    pub transaction: String,
    pub expected_cell: String,
    pub actual_cell: String,
    pub value: i64,
    pub sequence: u64,
    pub subject: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct HeapCell {
    id: String,
    value: i64,
}

#[derive(Clone, Debug)]
struct TransactionContext {
    record: TransactionRecord,
    buffered_writes: BTreeMap<String, i64>,
    applied_writes: Vec<AppliedWrite>,
    commit_entries: Vec<(String, usize, i64)>,
    pass: Option<ActuationPass>,
    acquired_odd_epoch: Option<u64>,
    published_early: bool,
}

pub struct StmRun {
    cell_registry: ResourceRegistry<usize>,
    transaction_registry: ResourceRegistry<usize>,
    access_graph: RelationshipGraph,
    specs: BTreeMap<String, TransactionSpec>,
    initial_heap: BTreeMap<String, i64>,
    heap: Vec<HeapCell>,
    contexts: Vec<TransactionContext>,
    pub reads: Vec<ReadResult>,
    pub epoch_events: Vec<EpochEvent>,
    pub applied_writes: Vec<AppliedWrite>,
    pub trace: TraceLog,
    pub final_epoch: u64,
    step_subjects: Vec<String>,
}

impl StmRun {
    pub fn heap(&self) -> BTreeMap<String, i64> {
        self.heap
            .iter()
            .map(|cell| (cell.id.clone(), cell.value))
            .collect()
    }

    pub fn transactions(&self) -> Vec<TransactionRecord> {
        self.contexts
            .iter()
            .map(|context| context.record.clone())
            .collect()
    }

    pub fn opacity(&self) -> OpacityEvaluation {
        stm_reference::evaluate_opacity(&self.initial_heap, &self.heap(), &self.transactions())
    }
}

pub fn run_script(
    cells: &[CellSpec],
    transactions: &[TransactionSpec],
    steps: &[StmStep],
    control: StmControl,
) -> Result<StmRun, StructureError> {
    if cells.is_empty() || transactions.is_empty() || steps.is_empty() {
        return Err(StructureError::new(
            "FEX-DOM-TXN-01 requires cells, transaction declarations, and steps",
        ));
    }
    let mut trace = TraceLog::default();
    let cell_registry = ResourceRegistry::build(
        cells
            .iter()
            .enumerate()
            .map(|(index, cell)| (cell.id.clone(), index)),
        &mut trace,
        CELL_SUBJECT,
    )?;
    let mut heap = cells
        .iter()
        .map(|cell| HeapCell {
            id: cell.id.clone(),
            value: cell.initial,
        })
        .collect::<Vec<_>>();
    let initial_heap = cells
        .iter()
        .map(|cell| (cell.id.clone(), cell.initial))
        .collect::<BTreeMap<_, _>>();
    let specs = transactions
        .iter()
        .map(|spec| (spec.id.clone(), spec.clone()))
        .collect::<BTreeMap<_, _>>();
    if specs.len() != transactions.len() || specs.contains_key("") {
        return Err(StructureError::new(
            "transaction declarations require unique nonempty identities",
        ));
    }
    let access_graph = build_access_graph(transactions, &cell_registry, &mut trace)?;
    let mut transaction_registry = ResourceRegistry::empty(&mut trace, TXN_SUBJECT);
    let epoch = AtomicU64::new(0);
    let mut contexts = Vec::<TransactionContext>::new();
    let mut reads = Vec::new();
    let mut epoch_events = Vec::new();
    let mut applied_writes = Vec::new();
    let mut carrier = Sequential::new(
        steps.len() as u64,
        "initialized".to_string(),
        &mut trace,
        RUN_SUBJECT,
    )?;
    let mut step_subjects = Vec::new();

    for (index, instruction) in steps.iter().enumerate() {
        let subject = format!("FEX-DOM-TXN-01::step-{index}");
        step_subjects.push(subject.clone());
        let step = carrier.begin_step(&mut trace, &subject)?;
        match instruction {
            StmStep::Begin { transaction } => begin_transaction(
                transaction,
                index as u64,
                control,
                &specs,
                &epoch,
                &mut contexts,
                &mut transaction_registry,
                &mut trace,
                &subject,
            )?,
            StmStep::Read { transaction, cell } => read_cell(
                transaction,
                cell,
                index as u64,
                control,
                &cell_registry,
                &access_graph,
                &epoch,
                &heap,
                &transaction_registry,
                &mut contexts,
                &mut reads,
            )?,
            StmStep::Write {
                transaction,
                cell,
                value,
            } => buffer_write(
                transaction,
                cell,
                *value,
                index as u64,
                control,
                &cell_registry,
                &access_graph,
                &transaction_registry,
                &mut contexts,
            )?,
            StmStep::CommitBegin { transaction } => begin_commit(
                transaction,
                index as u64,
                control,
                &cell_registry,
                &epoch,
                &transaction_registry,
                &mut contexts,
                &mut epoch_events,
                &mut trace,
                &subject,
            )?,
            StmStep::ApplyNext { transaction } => apply_next_write(
                transaction,
                index as u64,
                control,
                &epoch,
                &transaction_registry,
                &mut contexts,
                &mut heap,
                &mut epoch_events,
                &mut applied_writes,
                &mut trace,
                &subject,
            )?,
            StmStep::CommitFinish { transaction } => finish_commit(
                transaction,
                index as u64,
                control,
                &epoch,
                &transaction_registry,
                &mut contexts,
                &mut epoch_events,
                &mut trace,
                &subject,
            )?,
        }
        carrier.complete_step(step, format!("completed-{index}"), &mut trace, &subject)?;
    }
    carrier.done_stuttering(&mut trace, RUN_SUBJECT)?;

    Ok(StmRun {
        cell_registry,
        transaction_registry,
        access_graph,
        specs,
        initial_heap,
        heap,
        contexts,
        reads,
        epoch_events,
        applied_writes,
        trace,
        final_epoch: epoch.load(Ordering::SeqCst),
        step_subjects,
    })
}

fn build_access_graph(
    transactions: &[TransactionSpec],
    cells: &ResourceRegistry<usize>,
    trace: &mut TraceLog,
) -> Result<RelationshipGraph, StructureError> {
    let mut vertices = cells
        .ids()
        .map(|cell| format!("cell:{cell}"))
        .collect::<Vec<_>>();
    vertices.extend(
        transactions
            .iter()
            .map(|transaction| format!("txn:{}", transaction.id)),
    );
    let mut edges = Vec::new();
    for transaction in transactions {
        let mut declared = BTreeSet::new();
        for (cell, mode) in &transaction.accesses {
            if !cells.contains(cell) || !declared.insert(cell.clone()) {
                return Err(StructureError::new(format!(
                    "transaction {} has an unknown or duplicate access {cell}",
                    transaction.id
                )));
            }
            edges.push(Edge {
                from: format!("txn:{}", transaction.id),
                to: format!("cell:{cell}"),
                weight: mode.weight(),
            });
        }
    }
    RelationshipGraph::build(vertices, edges, trace, GRAPH_SUBJECT)
}

#[allow(clippy::too_many_arguments)]
fn begin_transaction(
    requested_id: &str,
    sequence: u64,
    control: StmControl,
    specs: &BTreeMap<String, TransactionSpec>,
    epoch: &AtomicU64,
    contexts: &mut Vec<TransactionContext>,
    registry: &mut ResourceRegistry<usize>,
    trace: &mut TraceLog,
    subject: &str,
) -> Result<(), StructureError> {
    if !specs.contains_key(requested_id) {
        return Err(StructureError::new(format!(
            "unknown transaction declaration {requested_id}"
        )));
    }
    let effective_id = if control == StmControl::ReuseTransactionIdentity && !registry.is_empty() {
        registry
            .ids()
            .next()
            .expect("nonempty transaction registry")
            .clone()
    } else {
        requested_id.to_string()
    };
    let start_epoch = epoch.load(Ordering::SeqCst);
    let status = if start_epoch.is_multiple_of(2) {
        TransactionStatus::Active
    } else {
        TransactionStatus::Aborted
    };
    let index = contexts.len();
    registry.insert(effective_id.clone(), index, trace, subject)?;
    contexts.push(TransactionContext {
        record: TransactionRecord {
            id: effective_id,
            begin_sequence: sequence,
            end_sequence: (status == TransactionStatus::Aborted).then_some(sequence),
            start_epoch,
            status,
            operations: Vec::new(),
        },
        buffered_writes: BTreeMap::new(),
        applied_writes: Vec::new(),
        commit_entries: Vec::new(),
        pass: None,
        acquired_odd_epoch: None,
        published_early: false,
    });
    Ok(())
}

fn context_index(
    transaction: &str,
    registry: &ResourceRegistry<usize>,
) -> Result<usize, StructureError> {
    registry
        .get(transaction)
        .copied()
        .ok_or_else(|| StructureError::new(format!("unknown transaction {transaction}")))
}

fn declared_mode(graph: &RelationshipGraph, transaction: &str, cell: &str) -> Option<AccessMode> {
    graph
        .outgoing(&format!("txn:{transaction}"))
        .iter()
        .find(|edge| edge.to == format!("cell:{cell}"))
        .and_then(|edge| match edge.weight {
            1 => Some(AccessMode::Read),
            2 => Some(AccessMode::Write),
            3 => Some(AccessMode::ReadWrite),
            _ => None,
        })
}

#[allow(clippy::too_many_arguments)]
fn read_cell(
    transaction: &str,
    cell: &str,
    sequence: u64,
    control: StmControl,
    cells: &ResourceRegistry<usize>,
    graph: &RelationshipGraph,
    epoch: &AtomicU64,
    heap: &[HeapCell],
    registry: &ResourceRegistry<usize>,
    contexts: &mut [TransactionContext],
    reads: &mut Vec<ReadResult>,
) -> Result<(), StructureError> {
    let index = context_index(transaction, registry)?;
    let context = &mut contexts[index];
    if context.record.status != TransactionStatus::Active {
        return Ok(());
    }
    let declared =
        declared_mode(graph, &context.record.id, cell).is_some_and(|mode| mode.permits_read());
    if !declared && control != StmControl::UndeclaredAccess {
        return Err(StructureError::new(format!(
            "transaction {} did not declare read access to {cell}",
            context.record.id
        )));
    }
    let value = if let Some(value) = context.buffered_writes.get(cell) {
        *value
    } else {
        let before = epoch.load(Ordering::SeqCst);
        if control != StmControl::IgnoreEpochValidation
            && (before != context.record.start_epoch || !before.is_multiple_of(2))
        {
            abort_context(context, sequence);
            return Ok(());
        }
        let cell_index = cells
            .get(cell)
            .copied()
            .ok_or_else(|| StructureError::new(format!("unknown cell {cell}")))?;
        let value = heap[cell_index].value;
        let after = epoch.load(Ordering::SeqCst);
        if control != StmControl::IgnoreEpochValidation
            && (after != before || after != context.record.start_epoch || !after.is_multiple_of(2))
        {
            abort_context(context, sequence);
            return Ok(());
        }
        value
    };
    context.record.operations.push(TxnOperation::Read {
        cell: cell.to_string(),
        value,
        sequence,
    });
    reads.push(ReadResult {
        transaction: context.record.id.clone(),
        cell: cell.to_string(),
        value,
        sequence,
    });
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn buffer_write(
    transaction: &str,
    cell: &str,
    value: i64,
    sequence: u64,
    control: StmControl,
    cells: &ResourceRegistry<usize>,
    graph: &RelationshipGraph,
    registry: &ResourceRegistry<usize>,
    contexts: &mut [TransactionContext],
) -> Result<(), StructureError> {
    let index = context_index(transaction, registry)?;
    let context = &mut contexts[index];
    if context.record.status != TransactionStatus::Active {
        return Ok(());
    }
    let declared =
        declared_mode(graph, &context.record.id, cell).is_some_and(|mode| mode.permits_write());
    if !declared && control != StmControl::UndeclaredAccess {
        return Err(StructureError::new(format!(
            "transaction {} did not declare write access to {cell}",
            context.record.id
        )));
    }
    if !cells.contains(cell) {
        return Err(StructureError::new(format!("unknown cell {cell}")));
    }
    context.buffered_writes.insert(cell.to_string(), value);
    context.record.operations.push(TxnOperation::Write {
        cell: cell.to_string(),
        value,
        sequence,
    });
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn begin_commit(
    transaction: &str,
    sequence: u64,
    control: StmControl,
    cells: &ResourceRegistry<usize>,
    epoch: &AtomicU64,
    registry: &ResourceRegistry<usize>,
    contexts: &mut [TransactionContext],
    events: &mut Vec<EpochEvent>,
    trace: &mut TraceLog,
    subject: &str,
) -> Result<(), StructureError> {
    let index = context_index(transaction, registry)?;
    let context = &mut contexts[index];
    if context.record.status != TransactionStatus::Active {
        return Ok(());
    }
    if context.buffered_writes.is_empty() {
        let observed = epoch.load(Ordering::SeqCst);
        events.push(EpochEvent {
            transaction: context.record.id.clone(),
            action: EpochAction::ValidateReadOnly,
            before: observed,
            after: observed,
            sequence,
        });
        if control != StmControl::IgnoreEpochValidation
            && (observed != context.record.start_epoch || !observed.is_multiple_of(2))
        {
            abort_context(context, sequence);
        } else {
            context.record.status = TransactionStatus::PreparedReadOnly;
        }
        return Ok(());
    }

    let start = context.record.start_epoch;
    let acquired =
        match epoch.compare_exchange(start, start + 1, Ordering::SeqCst, Ordering::SeqCst) {
            Ok(before) => Some((before, start + 1)),
            Err(current)
                if control == StmControl::AllowConflictingCommit && current.is_multiple_of(2) =>
            {
                epoch
                    .compare_exchange(current, current + 1, Ordering::SeqCst, Ordering::SeqCst)
                    .ok()
                    .map(|before| (before, current + 1))
            }
            Err(_) => None,
        };
    let Some((before, odd)) = acquired else {
        abort_context(context, sequence);
        return Ok(());
    };
    events.push(EpochEvent {
        transaction: context.record.id.clone(),
        action: EpochAction::Acquire,
        before,
        after: odd,
        sequence,
    });
    context.acquired_odd_epoch = Some(odd);
    context.commit_entries = context
        .buffered_writes
        .iter()
        .map(|(cell, value)| {
            cells
                .get(cell)
                .copied()
                .map(|index| (cell.clone(), index, *value))
                .ok_or_else(|| StructureError::new(format!("unknown write cell {cell}")))
        })
        .collect::<Result<Vec<_>, _>>()?;
    if control == StmControl::OmitWriteTarget && context.commit_entries.len() > 1 {
        context.commit_entries.pop();
    }
    let mut allocation = context
        .commit_entries
        .iter()
        .map(|(_, cell, _)| Some(*cell))
        .collect::<Vec<_>>();
    if control == StmControl::MisdirectWrite && !allocation.is_empty() && cells.len() > 1 {
        let selected = allocation[0].expect("allocated write target");
        allocation[0] = Some((selected + 1) % cells.len());
    }
    context.pass = Some(ActuationPass::new(allocation, trace, subject));
    context.record.status = TransactionStatus::Committing;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn apply_next_write(
    transaction: &str,
    sequence: u64,
    control: StmControl,
    epoch: &AtomicU64,
    registry: &ResourceRegistry<usize>,
    contexts: &mut [TransactionContext],
    heap: &mut [HeapCell],
    events: &mut Vec<EpochEvent>,
    all_applied: &mut Vec<AppliedWrite>,
    trace: &mut TraceLog,
    subject: &str,
) -> Result<(), StructureError> {
    let index = context_index(transaction, registry)?;
    let context = &mut contexts[index];
    if context.record.status != TransactionStatus::Committing {
        return Ok(());
    }
    let seat = context.applied_writes.len();
    let Some((expected_cell, _, value)) = context.commit_entries.get(seat).cloned() else {
        return Ok(());
    };
    let pass = context
        .pass
        .as_mut()
        .ok_or_else(|| StructureError::new("committing transaction has no ActuationPass"))?;
    let actual_index = pass.actuate_with(
        seat,
        heap,
        |cell, _, _| {
            cell.value = value;
            Ok(())
        },
        trace,
        subject,
    )?;
    let applied = AppliedWrite {
        transaction: context.record.id.clone(),
        expected_cell,
        actual_cell: heap[actual_index].id.clone(),
        value,
        sequence,
        subject: subject.to_string(),
    };
    context.applied_writes.push(applied.clone());
    all_applied.push(applied);

    if control == StmControl::PublishBeforeAllWrites && !context.published_early {
        let odd = context
            .acquired_odd_epoch
            .ok_or_else(|| StructureError::new("write transaction did not acquire the epoch"))?;
        epoch.store(odd + 1, Ordering::SeqCst);
        events.push(EpochEvent {
            transaction: context.record.id.clone(),
            action: EpochAction::Publish,
            before: odd,
            after: odd + 1,
            sequence,
        });
        context.published_early = true;
    }
    if control == StmControl::PartialAbortAfterWrite && context.applied_writes.len() == 1 {
        if !context.published_early {
            let odd = context.acquired_odd_epoch.ok_or_else(|| {
                StructureError::new("write transaction did not acquire the epoch")
            })?;
            epoch.store(odd + 1, Ordering::SeqCst);
            events.push(EpochEvent {
                transaction: context.record.id.clone(),
                action: EpochAction::Publish,
                before: odd,
                after: odd + 1,
                sequence,
            });
        }
        abort_context(context, sequence);
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn finish_commit(
    transaction: &str,
    sequence: u64,
    control: StmControl,
    epoch: &AtomicU64,
    registry: &ResourceRegistry<usize>,
    contexts: &mut [TransactionContext],
    events: &mut Vec<EpochEvent>,
    trace: &mut TraceLog,
    subject: &str,
) -> Result<(), StructureError> {
    let index = context_index(transaction, registry)?;
    let context = &mut contexts[index];
    match context.record.status {
        TransactionStatus::PreparedReadOnly => {
            let observed = epoch.load(Ordering::SeqCst);
            if control != StmControl::IgnoreEpochValidation
                && (observed != context.record.start_epoch || !observed.is_multiple_of(2))
            {
                abort_context(context, sequence);
            } else {
                context.record.status = TransactionStatus::Committed;
                context.record.end_sequence = Some(sequence);
            }
        }
        TransactionStatus::Committing => {
            let pass = context.pass.as_mut().ok_or_else(|| {
                StructureError::new("committing transaction has no ActuationPass")
            })?;
            if context.applied_writes.len() != context.commit_entries.len() {
                return Err(StructureError::new(format!(
                    "transaction {} has unapplied write targets",
                    context.record.id
                )));
            }
            pass.finish(trace, subject)?;
            if !context.published_early {
                let odd = context.acquired_odd_epoch.ok_or_else(|| {
                    StructureError::new("write transaction did not acquire the epoch")
                })?;
                epoch.store(odd + 1, Ordering::SeqCst);
                events.push(EpochEvent {
                    transaction: context.record.id.clone(),
                    action: EpochAction::Publish,
                    before: odd,
                    after: odd + 1,
                    sequence,
                });
            }
            context.record.status = TransactionStatus::Committed;
            context.record.end_sequence = Some(sequence);
        }
        TransactionStatus::Active | TransactionStatus::Committed | TransactionStatus::Aborted => {}
    }
    Ok(())
}

fn abort_context(context: &mut TransactionContext, sequence: u64) {
    context.record.status = TransactionStatus::Aborted;
    context.record.end_sequence = Some(sequence);
}

pub fn verify_run(run: &StmRun) -> Result<OpacityEvaluation, StructureError> {
    if !run.final_epoch.is_multiple_of(2) {
        return Err(StructureError::new(
            "terminal global epoch is not quiescent",
        ));
    }
    if run.cell_registry.len() != run.initial_heap.len()
        || run.transaction_registry.len() != run.contexts.len()
    {
        return Err(StructureError::new(
            "identity registries differ from authoritative runtime state",
        ));
    }
    run.trace
        .require_single_event_for(Structure::RelationshipGraph, "Commit", GRAPH_SUBJECT)?;
    run.trace
        .require_single_event_for(Structure::Sequential, "Done", RUN_SUBJECT)?;
    for subject in &run.step_subjects {
        let begin = run
            .trace
            .require_single_event_for(Structure::Sequential, "Begin", subject)?;
        let complete =
            run.trace
                .require_single_event_for(Structure::Sequential, "Complete", subject)?;
        if begin.sequence >= complete.sequence {
            return Err(StructureError::new(format!(
                "sequential step is misordered for {subject}"
            )));
        }
    }
    for context in &run.contexts {
        if matches!(
            context.record.status,
            TransactionStatus::Active
                | TransactionStatus::Committing
                | TransactionStatus::PreparedReadOnly
        ) {
            return Err(StructureError::new(format!(
                "transaction {} is not terminal",
                context.record.id
            )));
        }
        let spec = run.specs.get(&context.record.id).ok_or_else(|| {
            StructureError::new(format!(
                "missing transaction declaration {}",
                context.record.id
            ))
        })?;
        for (cell, mode) in &spec.accesses {
            if declared_mode(&run.access_graph, &spec.id, cell) != Some(*mode) {
                return Err(StructureError::new(format!(
                    "access graph differs from transaction {} declaration for {cell}",
                    spec.id
                )));
            }
        }
        for operation in &context.record.operations {
            let (cell, required_read) = match operation {
                TxnOperation::Read { cell, .. } => (cell, true),
                TxnOperation::Write { cell, .. } => (cell, false),
            };
            let mode =
                declared_mode(&run.access_graph, &context.record.id, cell).ok_or_else(|| {
                    StructureError::new(format!(
                        "transaction {} used undeclared cell {cell}",
                        context.record.id
                    ))
                })?;
            if (required_read && !mode.permits_read()) || (!required_read && !mode.permits_write())
            {
                return Err(StructureError::new(format!(
                    "transaction {} used the wrong access mode for {cell}",
                    context.record.id
                )));
            }
        }
        if context.record.status == TransactionStatus::Aborted && !context.applied_writes.is_empty()
        {
            return Err(StructureError::new(format!(
                "aborted transaction {} applied shared writes",
                context.record.id
            )));
        }
        let expected_writes = context
            .buffered_writes
            .iter()
            .map(|(cell, value)| (cell.clone(), *value))
            .collect::<BTreeSet<_>>();
        let applied_writes = context
            .applied_writes
            .iter()
            .map(|write| (write.actual_cell.clone(), write.value))
            .collect::<BTreeSet<_>>();
        if context.record.status == TransactionStatus::Committed
            && !expected_writes.is_empty()
            && applied_writes != expected_writes
        {
            return Err(StructureError::new(format!(
                "committed transaction {} did not apply its exact write set",
                context.record.id
            )));
        }
        if context.record.status == TransactionStatus::Committed && !expected_writes.is_empty() {
            let acquire = run
                .epoch_events
                .iter()
                .find(|event| {
                    event.transaction == context.record.id && event.action == EpochAction::Acquire
                })
                .ok_or_else(|| StructureError::new("committed writer has no epoch acquisition"))?;
            let publish = run
                .epoch_events
                .iter()
                .find(|event| {
                    event.transaction == context.record.id && event.action == EpochAction::Publish
                })
                .ok_or_else(|| StructureError::new("committed writer has no epoch publication"))?;
            if acquire.before != context.record.start_epoch
                || acquire.after != acquire.before + 1
                || acquire.after.is_multiple_of(2)
                || publish.before != acquire.after
                || publish.after != acquire.after + 1
                || !publish.after.is_multiple_of(2)
                || publish.sequence <= acquire.sequence
            {
                return Err(StructureError::new(format!(
                    "transaction {} has an invalid atomic epoch transition",
                    context.record.id
                )));
            }
            if context.applied_writes.iter().any(|write| {
                write.sequence <= acquire.sequence || write.sequence >= publish.sequence
            }) {
                return Err(StructureError::new(format!(
                    "transaction {} published outside its complete write interval",
                    context.record.id
                )));
            }
            let pass = context
                .pass
                .as_ref()
                .ok_or_else(|| StructureError::new("committed writer has no ActuationPass"))?;
            if !pass.is_complete() || pass.allocation() != pass.effects() {
                return Err(StructureError::new(format!(
                    "transaction {} has incomplete target-bound actuation",
                    context.record.id
                )));
            }
        }
    }
    for applied in &run.applied_writes {
        let begin =
            run.trace
                .require_single_event_for(Structure::Sequential, "Begin", &applied.subject)?;
        let effect = run.trace.require_single_event_for(
            Structure::ActuationPass,
            "Commit",
            &applied.subject,
        )?;
        let complete = run.trace.require_single_event_for(
            Structure::Sequential,
            "Complete",
            &applied.subject,
        )?;
        if !(begin.sequence < effect.sequence && effect.sequence < complete.sequence) {
            return Err(StructureError::new(format!(
                "write actuation is misordered for {}",
                applied.subject
            )));
        }
        if applied.expected_cell != applied.actual_cell {
            return Err(StructureError::new(format!(
                "write effect targeted {} instead of {}",
                applied.actual_cell, applied.expected_cell
            )));
        }
    }
    let opacity = run.opacity();
    if !opacity.accepted {
        return Err(StructureError::new(
            "finite transaction history has no opaque serialization",
        ));
    }
    Ok(opacity)
}

pub fn atomic_pair_case() -> (Vec<CellSpec>, Vec<TransactionSpec>, Vec<StmStep>) {
    let cells = vec![CellSpec::new("x", 0), CellSpec::new("y", 0)];
    let transactions = vec![
        TransactionSpec::new("reader", [("x", AccessMode::Read), ("y", AccessMode::Read)]),
        TransactionSpec::new(
            "writer",
            [("x", AccessMode::Write), ("y", AccessMode::Write)],
        ),
    ];
    let steps = vec![
        StmStep::begin("reader"),
        StmStep::begin("writer"),
        StmStep::write("writer", "x", 1),
        StmStep::write("writer", "y", 1),
        StmStep::commit_begin("writer"),
        StmStep::apply_next("writer"),
        StmStep::read("reader", "x"),
        StmStep::read("reader", "y"),
        StmStep::commit_begin("reader"),
        StmStep::commit_finish("reader"),
        StmStep::apply_next("writer"),
        StmStep::commit_finish("writer"),
    ];
    (cells, transactions, steps)
}

pub fn early_publication_case() -> (Vec<CellSpec>, Vec<TransactionSpec>, Vec<StmStep>) {
    let cells = vec![CellSpec::new("x", 0), CellSpec::new("y", 0)];
    let transactions = vec![
        TransactionSpec::new(
            "writer",
            [("x", AccessMode::Write), ("y", AccessMode::Write)],
        ),
        TransactionSpec::new("reader", [("x", AccessMode::Read), ("y", AccessMode::Read)]),
    ];
    let steps = vec![
        StmStep::begin("writer"),
        StmStep::write("writer", "x", 1),
        StmStep::write("writer", "y", 1),
        StmStep::commit_begin("writer"),
        StmStep::apply_next("writer"),
        StmStep::begin("reader"),
        StmStep::read("reader", "x"),
        StmStep::read("reader", "y"),
        StmStep::commit_begin("reader"),
        StmStep::commit_finish("reader"),
        StmStep::apply_next("writer"),
        StmStep::commit_finish("writer"),
    ];
    (cells, transactions, steps)
}

pub fn conflicting_writers_case() -> (Vec<CellSpec>, Vec<TransactionSpec>, Vec<StmStep>) {
    let cells = vec![CellSpec::new("x", 0)];
    let transactions = vec![
        TransactionSpec::new("first", [("x", AccessMode::ReadWrite)]),
        TransactionSpec::new("second", [("x", AccessMode::ReadWrite)]),
    ];
    let steps = vec![
        StmStep::begin("first"),
        StmStep::begin("second"),
        StmStep::read("first", "x"),
        StmStep::read("second", "x"),
        StmStep::write("first", "x", 1),
        StmStep::write("second", "x", 2),
        StmStep::commit_begin("first"),
        StmStep::apply_next("first"),
        StmStep::commit_finish("first"),
        StmStep::commit_begin("second"),
        StmStep::apply_next("second"),
        StmStep::commit_finish("second"),
    ];
    (cells, transactions, steps)
}

pub fn undeclared_access_case() -> (Vec<CellSpec>, Vec<TransactionSpec>, Vec<StmStep>) {
    let cells = vec![CellSpec::new("x", 0), CellSpec::new("y", 0)];
    let transactions = vec![TransactionSpec::new("reader", [("x", AccessMode::Read)])];
    let steps = vec![
        StmStep::begin("reader"),
        StmStep::read("reader", "y"),
        StmStep::commit_begin("reader"),
        StmStep::commit_finish("reader"),
    ];
    (cells, transactions, steps)
}

pub fn expected_control_rejection(control: StmControl) -> Option<&'static str> {
    match control {
        StmControl::Honest => None,
        StmControl::ReuseTransactionIdentity => Some("cannot replace existing ID"),
        StmControl::UndeclaredAccess => Some("used undeclared cell"),
        StmControl::IgnoreEpochValidation => {
            Some("finite transaction history has no opaque serialization")
        }
        StmControl::AllowConflictingCommit => Some("invalid atomic epoch transition"),
        StmControl::OmitWriteTarget | StmControl::MisdirectWrite => {
            Some("did not apply its exact write set")
        }
        StmControl::PublishBeforeAllWrites => Some("published outside its complete write interval"),
        StmControl::PartialAbortAfterWrite => Some("applied shared writes"),
    }
}

pub fn control_is_detected(control: StmControl) -> bool {
    let Some(expected) = expected_control_rejection(control) else {
        return false;
    };
    let (cells, transactions, steps) = match control {
        StmControl::AllowConflictingCommit => conflicting_writers_case(),
        StmControl::PublishBeforeAllWrites => early_publication_case(),
        StmControl::ReuseTransactionIdentity => {
            let (cells, transactions, _) = conflicting_writers_case();
            (
                cells,
                transactions,
                vec![StmStep::begin("first"), StmStep::begin("second")],
            )
        }
        StmControl::UndeclaredAccess => undeclared_access_case(),
        _ => atomic_pair_case(),
    };
    let observed = match run_script(&cells, &transactions, &steps, control) {
        Err(error) => error.to_string(),
        Ok(run) => match verify_run(&run) {
            Err(error) => error.to_string(),
            Ok(_) => return false,
        },
    };
    observed.contains(expected)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_positive(case: (Vec<CellSpec>, Vec<TransactionSpec>, Vec<StmStep>)) -> StmRun {
        let (cells, transactions, steps) = case;
        let run = run_script(&cells, &transactions, &steps, StmControl::Honest).unwrap();
        verify_run(&run).unwrap();
        run
    }

    #[test]
    fn reader_cannot_observe_a_partial_write_batch() {
        let run = run_positive(atomic_pair_case());
        assert_eq!(
            run.heap(),
            BTreeMap::from([("x".to_string(), 1), ("y".to_string(), 1)])
        );
        assert_eq!(run.reads.len(), 0);
        let records = run.transactions();
        assert_eq!(records[0].status, TransactionStatus::Aborted);
        assert_eq!(records[1].status, TransactionStatus::Committed);
        assert!(run.opacity().accepted);
    }

    #[test]
    fn one_of_two_conflicting_writers_aborts() {
        let run = run_positive(conflicting_writers_case());
        let records = run.transactions();
        assert_eq!(records[0].status, TransactionStatus::Committed);
        assert_eq!(records[1].status, TransactionStatus::Aborted);
        assert_eq!(run.heap().get("x"), Some(&1));
    }

    #[test]
    fn early_publication_exposes_a_nonopaque_view() {
        let (cells, transactions, steps) = early_publication_case();
        let run = run_script(
            &cells,
            &transactions,
            &steps,
            StmControl::PublishBeforeAllWrites,
        )
        .unwrap();
        assert_eq!(
            run.reads.iter().map(|read| read.value).collect::<Vec<_>>(),
            [1, 0]
        );
        assert!(!run.opacity().accepted);
        assert!(verify_run(&run).is_err());
    }

    #[test]
    fn bypassing_epoch_validation_exposes_a_nonopaque_view() {
        let (cells, transactions, steps) = atomic_pair_case();
        let run = run_script(
            &cells,
            &transactions,
            &steps,
            StmControl::IgnoreEpochValidation,
        )
        .unwrap();
        assert_eq!(
            run.reads.iter().map(|read| read.value).collect::<Vec<_>>(),
            [1, 0]
        );
        assert!(!run.opacity().accepted);
        assert!(verify_run(&run).is_err());
    }

    #[test]
    fn stale_writers_cannot_both_commit() {
        let (cells, transactions, steps) = conflicting_writers_case();
        let run = run_script(
            &cells,
            &transactions,
            &steps,
            StmControl::AllowConflictingCommit,
        )
        .unwrap();
        assert!(run
            .transactions()
            .iter()
            .all(|record| record.status == TransactionStatus::Committed));
        assert!(!run.opacity().accepted);
        assert!(verify_run(&run).is_err());
    }

    #[test]
    fn every_registered_control_is_discriminating() {
        let controls = [
            StmControl::ReuseTransactionIdentity,
            StmControl::UndeclaredAccess,
            StmControl::IgnoreEpochValidation,
            StmControl::AllowConflictingCommit,
            StmControl::OmitWriteTarget,
            StmControl::MisdirectWrite,
            StmControl::PublishBeforeAllWrites,
            StmControl::PartialAbortAfterWrite,
        ];
        for control in controls {
            assert!(control_is_detected(control), "control escaped: {control:?}");
        }
    }

    #[test]
    fn every_local_order_preserving_two_writer_interleaving_is_opaque() {
        let first = vec![
            StmStep::begin("first"),
            StmStep::read("first", "x"),
            StmStep::write("first", "x", 1),
            StmStep::commit_begin("first"),
            StmStep::apply_next("first"),
            StmStep::commit_finish("first"),
        ];
        let second = vec![
            StmStep::begin("second"),
            StmStep::read("second", "x"),
            StmStep::write("second", "x", 2),
            StmStep::commit_begin("second"),
            StmStep::apply_next("second"),
            StmStep::commit_finish("second"),
        ];
        let mut schedules = Vec::new();
        enumerate_interleavings(&first, &second, Vec::new(), &mut schedules);
        assert_eq!(schedules.len(), 924);
        let cells = vec![CellSpec::new("x", 0)];
        let transactions = vec![
            TransactionSpec::new("first", [("x", AccessMode::ReadWrite)]),
            TransactionSpec::new("second", [("x", AccessMode::ReadWrite)]),
        ];
        for steps in schedules {
            let run = run_script(&cells, &transactions, &steps, StmControl::Honest).unwrap();
            verify_run(&run).unwrap();
        }
    }

    fn enumerate_interleavings(
        left: &[StmStep],
        right: &[StmStep],
        prefix: Vec<StmStep>,
        output: &mut Vec<Vec<StmStep>>,
    ) {
        if left.is_empty() && right.is_empty() {
            output.push(prefix);
            return;
        }
        if let Some((first, rest)) = left.split_first() {
            let mut next = prefix.clone();
            next.push(first.clone());
            enumerate_interleavings(rest, right, next, output);
        }
        if let Some((first, rest)) = right.split_first() {
            let mut next = prefix;
            next.push(first.clone());
            enumerate_interleavings(left, rest, next, output);
        }
    }
}
