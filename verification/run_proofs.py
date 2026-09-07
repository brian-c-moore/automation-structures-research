#!/usr/bin/env python3
"""Discover and run the Automation Structure formal evidence.

Discovery, identity checks, self-tests, and proof execution run through the
pinned project container. All prover state is created beneath a temporary
directory and removed when the command exits.
"""

from __future__ import annotations

import argparse
import copy
import dataclasses
import fnmatch
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Iterable, Sequence


CONTAINER_MARKER = "AUTOMATION_STRUCTURE_PROOF_CONTAINER"
DEFAULT_PRIMARY_CONTAINER = Path("/source/automation-structure-research")
DEFAULT_AUTOMATION_STRUCTURES_CRATE_ROOT = Path("/opt/automation-structures")
AUTOMATION_STRUCTURES_MANIFEST = Path(
    "formal/implementation/AUTOMATION_STRUCTURES_CRATE.json"
)
AUTOMATION_STRUCTURES_ACTION_CONTROLS = Path(
    "formal/implementation/AUTOMATION_STRUCTURES_ACTION_CONTROLS.json"
)
RUNTIME_ROOT = Path("/work")
MUTATION_DETECTOR_SELF_TEST_ID = "mutation-detector-contract-removal-self-test"
VERUS_EXPECTED_SURVIVORS = frozenset()
SEQUENCE_THEOREM_NAMES = frozenset(
    {
        "AppendInjective",
        "AppendInjectiveSeq",
        "AppendIsConcat",
        "AppendProperties",
        "ConcatAdjacentSubSeq",
        "ConcatAssociative",
        "ConcatEmptySeq",
        "ConcatEqualIffEmpty",
        "ConcatInjectiveSeq",
        "ConcatProperties",
        "ConcatSimplifications",
        "ElementOfSeq",
        "EmptySeq",
        "EmptySingletonIsInjective",
        "ExceptSeq",
        "HeadTailAppend",
        "HeadTailOfSubSeq",
        "HeadTailProperties",
        "IsASeq",
        "LenProperties",
        "RangeConcatenation",
        "RangeEquality",
        "RangeOfSeq",
        "SeqDef",
        "SeqEqual",
        "SeqMonotonic",
        "SeqOfRange",
        "SequenceEmptyOrAppend",
        "SequencesInductionAppend",
        "SequencesInductionTail",
        "SubSeqEmpty",
        "SubSeqOfConcat1",
        "SubSeqOfConcat2",
        "SubSeqOfSubSeq",
        "SubSeqProperties",
        "SubSeqRange",
        "SubSeqRecursive",
        "SubSeqRestrict",
        "TailInjectiveSeq",
        "TailIsSubSeq",
    }
)

KAT_RELATED_SUBJECTS: dict[str, tuple[str, ...]] = {
    "actuation_pass_kat": ("ActuationPass",),
    "audit_sink_kat": ("AuditSink",),
    "backtracking_traversal_kat": ("BacktrackingTraversal",),
    "bisection_kat": ("Bisection",),
    "budget_kat": ("Budget",),
    "competitive_selection_hard_exclusive_kat": ("CompetitiveSelection",),
    "competitive_selection_kat": ("CompetitiveSelection",),
    "equivalence_class_kat": ("EquivalenceClass",),
    "federated_budget_kat": ("FederatedBudget",),
    "fork_join_modality_kat": ("ForkJoin",),
    "governed_commit_bridge_kat": ("GovernedCommit",),
    "propagation_pass_kat": ("PropagationPass",),
    "quality_hierarchy_kat": ("QualityHierarchy",),
    "reduction_kat": ("Reduction",),
    "relationship_graph_kat": ("RelationshipGraph",),
    "sampler_kat": ("Sampler",),
    "sequential_modality_kat": ("Sequential",),
    "step_graph_modality_kat": ("StepGraph",),
    "stream_graph_fanout_modality_kat": ("StreamGraphFanout",),
    "stream_graph_modality_kat": ("StreamGraph",),
    "traversal_engine_kat": ("TraversalEngine",),
    "primitives_kat": (
        "ActuationPass",
        "AllocationSnapshot",
        "AuditSink",
        "BacktrackingTraversal",
        "Bisection",
        "Budget",
        "CompetitiveSelection",
        "ConvergenceGovernor",
        "EquivalenceClass",
        "FederatedBudget",
        "PropagationPass",
        "QualityHierarchy",
        "RateLimit",
        "Reduction",
        "RelationshipGraph",
        "ResourceRegistry",
        "Sampler",
        "SelectThenActuate",
        "Signal",
        "TraversalBudgetComposition",
        "TraversalEngine",
    ),
}

GOVERNED_COMMIT_ROLE_BINDINGS = (
    "use crate::modalities::sequential::Sequential;",
    "use crate::primitives::actuation_pass::ActuationPass;",
    "use crate::primitives::audit_sink::AuditSink;",
    "use crate::primitives::budget::Budget;",
    "use crate::primitives::propagation_pass::PropagationPass;",
    "use crate::primitives::propagation_pass::Round;",
    "use crate::primitives::resource_registry::ResourceRegistry;",
)

GOVERNED_COMMIT_DIRECT_REFINEMENT_FRAGMENTS = (
    "pub open spec fn abstract_system_step",
    "pub open spec fn abstract_failure_step",
    "pub open spec fn abstract_commit_step",
    "pub open spec fn abstract_stutter_step",
    "pub open spec fn abstract_observation_agrees",
    "accepted ==> Self::abstract_system_step(old(self), final(self))",
    "!accepted ==> Self::abstract_failure_step(old(self), final(self))",
    "Self::abstract_commit_step(old(self), final(self))",
    "Self::abstract_stutter_step(old(self), final(self))",
)

GOVERNED_COMMIT_METHOD_BINDINGS: dict[str, dict[str, tuple[str, ...]]] = {
    "new": {
        "actions": ("Init",),
        "rust": (
            "ResourceRegistry::new()",
            "Budget::new(capacity)",
            "Budget::new(max_attempts)",
            "PropagationPass::new(1, 1, 0, edges, values)",
            "ActuationPass::new(allocation, 1)",
            "AuditSink::new(1)",
            "Sequential::new(3, 4, 0)",
            "phase: CommitPhase::Pending",
        ),
        "tla": ("phase = \"Pending\"", "reserved = 0", "allocated = 0", "registryMapped"),
    },
    "admit": {
        "actions": ("AdmitAccepted", "AdmitRejected"),
        "rust": ("self.budget.reserve(1)", "CommitPhase::Admitted", "CommitPhase::Rejected"),
        "tla": ("reserved' = 1", "phase' = \"Admitted\"", "phase' = \"Rejected\""),
    },
    "propagate": {
        "actions": ("Propagate",),
        "rust": (
            "self.propagation.start_round()",
            "self.propagation.update_node(0)",
            "self.propagation.end_round()",
            "CommitPhase::Ready",
        ),
        "tla": ("propagationIteration' = 1", "phase' = \"Ready\"", "pc' = 2"),
    },
    "fail_before_effect": {
        "actions": ("FailBeforeEffect",),
        "rust": (
            "self.attempt_budget.try_allocate(1)",
            "CommitPhase::Retryable",
            "CommitPhase::Rejected",
        ),
        "tla": ("attempts' = attempts + 1", "\"Rejected\" ELSE \"Retryable\""),
    },
    "fail_after_effect": {
        "actions": ("FailAfterEffect",),
        "rust": (
            "self.attempt_budget.try_allocate(1)",
            "self.recovery_intent = true",
            "self.actuation.actuate(0)",
            "self.effect_applied = true",
            "CommitPhase::RecoveryPending",
        ),
        "tla": ("phase' = \"RecoveryPending\"", "effectApplied'", "recoveryIntent'"),
    },
    "commit_success": {
        "actions": ("CommitSuccess",),
        "rust": (
            "self.attempt_budget.try_allocate(1)",
            "self.actuation.actuate(0)",
            "self.budget.commit_reservation(1)",
            "self.audit.record(0)",
            "self.evidence_persisted = true",
            "CommitPhase::Committed",
        ),
        "tla": (
            "allocated' = 1",
            "reserved' = 0",
            "auditLen' = 1",
            "evidencePersisted'",
            "phase' = \"Committed\"",
        ),
    },
    "recover": {
        "actions": ("Recover",),
        "rust": (
            "self.budget.commit_reservation(1)",
            "self.audit.record(0)",
            "self.recovery_intent = false",
            "CommitPhase::Committed",
        ),
        "tla": ("phase = \"RecoveryPending\"", "auditLen' = 1", "recoveryIntent' = FALSE"),
    },
    "crash": {
        "actions": ("Crash",),
        "rust": ("self.crashed = true",),
        "tla": ("crashed'", "UNCHANGED <<phase, capacity, reserved, allocated"),
    },
    "restart": {
        "actions": ("Restart",),
        "rust": ("self.crashed = false",),
        "tla": ("crashed' = FALSE", "lastClass' = \"stutter\""),
    },
}


@dataclasses.dataclass(frozen=True)
class WorkItem:
    id: str
    scope: str
    area: str
    subject: str
    kind: str
    engine: str
    source: Path
    config: Path | None
    module: str | None
    expected: str
    purpose: str
    role: str = "evidence"
    expected_distinct: int | None = None
    expected_initial: int | None = None
    expected_obligations: int | None = None
    expected_failure: str | None = None
    mutation: Mutation | None = None
    related_subjects: tuple[str, ...] = ()

    def record(self, repository_root: Path) -> dict[str, object]:
        return {
            "id": self.id,
            "scope": self.scope,
            "area": self.area,
            "subject": self.subject,
            "related_subjects": list(self.related_subjects),
            "kind": self.kind,
            "engine": self.engine,
            "source": relative_display(self.source, repository_root),
            "config": (
                relative_display(self.config, repository_root)
                if self.config is not None
                else None
            ),
            "module": self.module,
            "expected": self.expected,
            "role": self.role,
            "expected_distinct": self.expected_distinct,
            "expected_initial": self.expected_initial,
            "expected_obligations": self.expected_obligations,
            "expected_failure": self.expected_failure,
            "mutation": self.mutation.record() if self.mutation is not None else None,
            "purpose": self.purpose,
        }


@dataclasses.dataclass
class RunResult:
    item: WorkItem
    status: str
    seconds: float
    signature: str
    command: list[str]
    output: str

    def record(self, repository_root: Path) -> dict[str, object]:
        record = self.item.record(repository_root)
        generated_states = None
        distinct_states = None
        tlaps_obligations = None
        verus_verified = None
        verus_errors = None
        failing_invariant = None
        if self.item.engine in {"tlc", "tlc-vector"}:
            generated_states, distinct_states = tlc_counts(self.output)
            failures = re.findall(
                r"Error: Invariant ([A-Za-z][A-Za-z0-9_]*) is violated",
                self.output,
            )
            failures.extend(
                re.findall(
                    r"Error: The invariant of ([A-Za-z][A-Za-z0-9_]*) is equal to FALSE",
                    self.output,
                )
            )
            failing_invariant = failures[-1] if failures else None
        if self.item.engine == "tlaps":
            obligations = re.findall(r"All ([0-9]+) obligations proved", self.output)
            tlaps_obligations = int(obligations[-1]) if obligations else None
        if self.item.engine in {"verus", "verus-control"}:
            matches = re.findall(
                r"verification results::\s*([0-9]+) verified,\s*([0-9]+) errors",
                self.output,
            )
            if matches:
                verus_verified, verus_errors = (int(value) for value in matches[-1])
        record.update(
            {
                "status": self.status,
                "seconds": round(self.seconds, 3),
                "signature": self.signature,
                "command": self.command,
                "generated_states": generated_states,
                "distinct_states": distinct_states,
                "tlaps_obligations": tlaps_obligations,
                "verus_verified": verus_verified,
                "verus_errors": verus_errors,
                "failing_invariant": failing_invariant,
            }
        )
        return record


@dataclasses.dataclass(frozen=True)
class Mutation:
    id: str
    subject: str
    source: str
    needle: str
    replacement: str
    purpose: str
    formal_module: str = ""
    executable_carrier: str = ""
    carried_obligation: str = ""
    affected_action: str = ""
    expected_fault: str = ""
    anchor_start: str | None = None
    anchor_end: str | None = None
    verification_root: str | None = None

    def record(self) -> dict[str, object]:
        return {
            "id": self.id,
            "subject": self.subject,
            "formal_module": self.formal_module,
            "executable_carrier": self.executable_carrier,
            "carried_obligation": self.carried_obligation,
            "affected_method_or_action": self.affected_action,
            "source": self.source,
            "exact_mutation_site": self.needle,
            "expected_fault": self.expected_fault,
            "anchor_start": self.anchor_start,
            "anchor_end": self.anchor_end,
            "verification_root": self.verification_root or self.source,
        }


VERUS_MUTATIONS = (
    Mutation(
        "actuation-pass-allocation-commit",
        "ActuationPass",
        "src/primitives/actuation_pass.rs",
        "        self.allocation.set(s, Some(resource));\n",
        "",
        "Requires Allocate to install the named resource at the selected seat.",
        formal_module="formal/structures/ActuationPass/ActuationPass.tla",
        executable_carrier="ActuationPass",
        carried_obligation="AllocationScope through the Allocate action relation",
        affected_action="allocate / Allocate",
        expected_fault="Allocate returns without installing the named seat allocation.",
        anchor_start="    pub fn allocate(&mut self, s: usize, resource: u64)",
        anchor_end="    /// TLA+ `Deallocate(s)`",
    ),
    Mutation(
        "actuation-pass-effect-fidelity",
        "ActuationPass",
        "src/primitives/actuation_pass.rs",
        "        self.effects.set(s, Some(resource));\n",
        "        self.effects.set(s, Some(0));\n",
        "Requires actuation to record the resource read from the live allocation.",
        formal_module="formal/structures/ActuationPass/ActuationPass.tla",
        executable_carrier="ActuationPass",
        carried_obligation="EffectFidelity through the Actuate action relation",
        affected_action="actuate / Actuate",
        expected_fault="The effect record may differ from the seat's allocated resource.",
        anchor_start="    pub fn actuate(&mut self, s: usize)",
        anchor_end="    /// TLA+ `Finish`",
    ),
    Mutation(
        "actuation-pass-scope-preservation",
        "ActuationPass",
        "src/primitives/actuation_pass.rs",
        "        self.allocation.set(s, None);\n",
        "        self.allocation.set(s, None);\n        self.effects.set(s, Some(0));\n",
        "Requires deallocation to preserve effect fidelity; actuation scope follows as a derived clause.",
        formal_module="formal/structures/ActuationPass/ActuationPass.tla",
        executable_carrier="ActuationPass",
        carried_obligation="EffectFidelity through Deallocate; ActuationScope is derived",
        affected_action="deallocate / Deallocate",
        expected_fault="Deallocation creates an effect for a seat whose allocation was removed.",
        anchor_start="    pub fn deallocate(&mut self, s: usize)",
        anchor_end="    // -- Pass and closure actions",
    ),
    Mutation(
        "actuation-pass-completion-commit",
        "ActuationPass",
        "src/primitives/actuation_pass.rs",
        "        self.complete = true;\n",
        "        self.complete = false;\n",
        "Requires Finish to record completion after every allocated seat has an effect.",
        formal_module="formal/structures/ActuationPass/ActuationPass.tla",
        executable_carrier="ActuationPass",
        carried_obligation="PassCompleteness through the Finish action relation",
        affected_action="finish / Finish",
        expected_fault="Finish returns without committing the complete flag.",
    ),
    Mutation(
        "bisection-converged-observation",
        "Bisection",
        "src/compositions/bisection.rs",
        "        self.hi - self.lo < 2\n",
        "        self.hi - self.lo >= 2\n",
        "Requires the executable convergence observation to equal the retained interval guard.",
        formal_module="formal/structures/Bisection/Bisection.tla",
        executable_carrier="Bisection",
        carried_obligation="Converged action guard",
        affected_action="converged / Converged",
        expected_fault="The executable convergence result is the negation of the modeled guard.",
        anchor_start="    pub fn converged(&self) -> (c: bool)",
        anchor_end="    /// Probe the midpoint",
    ),
    Mutation(
        "bisection-probe-budget",
        "Bisection",
        "src/compositions/bisection.rs",
        "        let _accepted = self.budget.try_allocate(1);\n",
        "        let _accepted = true;\n",
        "Requires the probe commit to advance from the prior count rather than exceed the ceiling.",
        formal_module="formal/structures/Bisection/Bisection.tla",
        executable_carrier="Bisection",
        carried_obligation="ProbeBound",
        affected_action="probe / ProbeLeft or ProbeRight",
        expected_fault="A probe records a count above the declared probe ceiling.",
    ),
    Mutation(
        "bisection-halving-endpoint",
        "Bisection",
        "src/compositions/bisection.rs",
        "            self.hi = mid;\n",
        "            self.hi = mid + 1;\n",
        "Requires the false-predicate branch to move the upper endpoint to the midpoint.",
        formal_module="formal/structures/Bisection/Bisection.tla",
        executable_carrier="Bisection",
        carried_obligation="Halving and the ProbeLeft action relation",
        affected_action="probe / ProbeLeft",
        expected_fault="The upper interval can remain wider than half the prior interval.",
    ),
    Mutation(
        "bisection-monotonicity-endpoint",
        "Bisection",
        "src/compositions/bisection.rs",
        "            self.lo = mid + 1;\n",
        "            self.lo = mid + 2;\n",
        "Requires the true-predicate branch to advance the lower endpoint by exactly one past midpoint.",
        formal_module="formal/structures/Bisection/Bisection.tla",
        executable_carrier="Bisection",
        carried_obligation="MonotonicityPreservation and the ProbeRight action relation",
        affected_action="probe / ProbeRight",
        expected_fault="The lower endpoint may advance past the threshold witness.",
    ),
    Mutation(
        "bisection-find-absence-completeness",
        "Bisection",
        "src/compositions/bisection.rs",
        "    n  // not present\n",
        "    lo  // wrong absence result\n",
        "Requires the applied binary search to return the sentinel only after excluding the target from every position.",
        formal_module="formal/structures/Bisection/Bisection.tla",
        executable_carrier="Bisection applied binary-search realization",
        carried_obligation="Complete absent-result observation",
        affected_action="bisection_find / terminal search observation",
        expected_fault="An absent target may return an in-range insertion point as though it were a matching index.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "competitive-selection-hard-exclusive-availability",
        "CompetitiveSelection",
        "src/primitives/competitive_selection.rs",
        "            if self.candidate_available(s, i) {",
        "            if true {",
        "Requires hard-exclusive selection to respect the live availability predicate.",
        formal_module="formal/structures/CompetitiveSelection/CompetitiveSelectionHardExclusive.tla",
        executable_carrier="CompetitiveSelection hard-exclusive variant",
        carried_obligation="HardWinnerOptimality and availability eligibility",
        affected_action="select_hard_exclusive / Select",
        expected_fault="An unavailable candidate may receive the exclusive allocation.",
    ),
    Mutation(
        "competitive-selection-hard-winner",
        "CompetitiveSelection",
        "src/primitives/competitive_selection.rs",
        "        self.allocation = Some(best);\n",
        "        self.allocation = None;\n",
        "Requires hard evaluation to commit its selected argmax.",
        formal_module="formal/structures/CompetitiveSelection/CompetitiveSelectionHardExclusive.tla",
        executable_carrier="CompetitiveSelection one-seat hard projection",
        carried_obligation="HardWinnerOptimality and HardWinnerTieBreak through Evaluate",
        affected_action="evaluate / Evaluate",
        expected_fault="Hard evaluation returns without committing the computed winner.",
    ),
    Mutation(
        "competitive-selection-hard-exclusive-shared-invalidation",
        "CompetitiveSelection",
        "src/primitives/competitive_selection.rs",
        "            self.allocation.set(t, None);\n",
        "",
        "Requires a coupled score update to invalidate every seat allocation.",
        formal_module="formal/structures/CompetitiveSelection/CompetitiveSelectionHardExclusive.tla",
        executable_carrier="CompetitiveSelection hard-exclusive shared-state variant",
        carried_obligation="Shared-state WinnerOptimality and MutualExclusion after UpdateScore",
        affected_action="update_score / UpdateScore",
        expected_fault="A score update leaves a stale allocation under the shared score matrix.",
    ),
    Mutation(
        "competitive-selection-soft-score-commit",
        "CompetitiveSelection",
        "src/primitives/competitive_selection.rs",
        "        self.scores.set(c, v);\n",
        "",
        "Requires mutable soft-score update to install the named candidate score.",
        formal_module="formal/structures/CompetitiveSelection/CompetitiveSelectionSoftMutableScores.tla",
        executable_carrier="CompetitiveSelection soft mutable-score variant",
        carried_obligation="MutableUpdateScore action relation",
        affected_action="CompetitiveSelectionSoft::update_score / MutableUpdateScore",
        expected_fault="The soft allocation reset occurs without installing the new score.",
        anchor_start="    /// CompetitiveSelectionSoftMutableScores `UpdateScore(c,v)`",
        anchor_end="// ── Ranked mode",
    ),
    Mutation(
        "competitive-selection-soft-award",
        "CompetitiveSelection",
        "src/primitives/competitive_selection.rs",
        "        self.extra.set(best, self.extra[best] + 1);\n",
        "",
        "Requires one AssignNext call to award the selected candidate's next unit.",
        formal_module="formal/structures/CompetitiveSelection/CompetitiveSelectionSoft.tla",
        executable_carrier="CompetitiveSelection soft variant",
        carried_obligation="SoftUniversalContribution, SoftScoreOrderPreservation, and AssignNext",
        affected_action="assign_next / AssignNext",
        expected_fault="The method returns a winner without advancing the soft allocation.",
    ),
    Mutation(
        "competitive-selection-soft-new-tie-trace",
        "CompetitiveSelection",
        "src/primitives/competitive_selection.rs",
        "                if lhs > rhs {\n",
        "                if lhs >= rhs {\n",
        "Requires batch construction to use the same lowest-index priority tie-break as repeated AssignNext.",
        formal_module="formal/structures/CompetitiveSelection/CompetitiveSelectionSoft.tla",
        executable_carrier="CompetitiveSelection soft batch constructor",
        carried_obligation="Exact deterministic AssignNext trace from Init",
        affected_action="CompetitiveSelectionSoft::new / Init followed by AssignNext",
        expected_fault="The batch constructor awards equal priorities to the highest visited index instead of the lowest index.",
        anchor_start="    pub fn new(scores: Vec<u64>, weight_total: u64, max_score: u64) -> (s: CompetitiveSelectionSoft)",
        anchor_end="    /// Award one further pool unit",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "competitive-selection-ranked-mark",
        "CompetitiveSelection",
        "src/primitives/competitive_selection.rs",
        "                    self.selected.set(m, true);\n",
        "",
        "Requires ranked selection to mark each chosen top candidate.",
        formal_module="formal/structures/CompetitiveSelection/CompetitiveSelectionRanked.tla",
        executable_carrier="CompetitiveSelection ranked variant",
        carried_obligation="RankedBoundedMultiplicity, RankedThresholdOptimality, and RankedTieBreak",
        affected_action="select / Select",
        expected_fault="Ranked selection omits a computed top candidate from the selected set.",
    ),
    Mutation(
        "competitive-selection-ranked-score-replacement",
        "CompetitiveSelection",
        "src/primitives/competitive_selection.rs",
        "        self.scores = new_scores;\n",
        "        let _ = new_scores;\n",
        "Requires ranked UpdateScores to install the complete caller-supplied score vector.",
        formal_module="formal/structures/CompetitiveSelection/CompetitiveSelectionRanked.tla",
        executable_carrier="CompetitiveSelection ranked variant",
        carried_obligation="Ranked UpdateScores action relation",
        affected_action="CompetitiveSelectionRanked::update_scores / UpdateScores",
        expected_fault="Ranked selection is cleared while the prior score vector remains live.",
    ),
    Mutation(
        "fork-join-start-state",
        "ForkJoin",
        "src/modalities/fork_join.rs",
        "            self.wstate.set(worker, ForkJoinWorkerState::Running);\n",
        "",
        "Requires StartWorker to advance the named ready worker to Running.",
        formal_module="formal/execution/carriers/ForkJoin.tla",
        executable_carrier="ForkJoin",
        carried_obligation="StartWorker action relation and PhaseOrdering",
        affected_action="start_worker / StartWorker",
        expected_fault="StartWorker reports acceptance without changing the worker state.",
    ),
    Mutation(
        "fork-join-complete-state",
        "ForkJoin",
        "src/modalities/fork_join.rs",
        "            self.wstate.set(worker, ForkJoinWorkerState::Complete);\n",
        "",
        "Requires CompleteWorker to advance the named running worker to Complete.",
        formal_module="formal/execution/carriers/ForkJoin.tla",
        executable_carrier="ForkJoin",
        carried_obligation="CompleteWorker action relation and BarrierCompleteness",
        affected_action="complete_worker / CompleteWorker",
        expected_fault="CompleteWorker records a value but leaves the worker running.",
    ),
    Mutation(
        "fork-join-barrier-phase",
        "ForkJoin",
        "src/modalities/fork_join.rs",
        "            self.phase = ForkJoinPhase::Join;\n",
        "",
        "Requires Barrier to commit the Fork-to-Join phase transition.",
        formal_module="formal/execution/carriers/ForkJoin.tla",
        executable_carrier="ForkJoin",
        carried_obligation="Barrier action relation and PhaseOrdering",
        affected_action="barrier / Barrier",
        expected_fault="Barrier reports acceptance while the carrier remains in Fork.",
    ),
    Mutation(
        "fork-join-early-output",
        "ForkJoin",
        "src/modalities/fork_join.rs",
        "        if matches!(self.phase, ForkJoinPhase::Join) {\n",
        "        if matches!(self.phase, ForkJoinPhase::Fork) {\n",
        "Requires output commit to occur at the join phase rather than during fork.",
        formal_module="formal/execution/carriers/ForkJoin.tla",
        executable_carrier="ForkJoin",
        carried_obligation="BarrierCompleteness and PhaseOrdering",
        affected_action="produce_output / ProduceOutput",
        expected_fault="Output commit occurs before the join barrier.",
    ),
    Mutation(
        "fork-join-stale-snapshot",
        "ForkJoin",
        "src/modalities/fork_join.rs",
        "            self.output_snapshot = self.wvalue.clone();\n",
        "",
        "Requires output commit to copy the completed worker snapshot.",
        formal_module="formal/execution/carriers/ForkJoin.tla",
        executable_carrier="ForkJoin",
        carried_obligation="OutputConsistency",
        affected_action="produce_output / ProduceOutput",
        expected_fault="Committed output does not copy the completed worker values.",
    ),
    Mutation(
        "fork-join-done-observation",
        "ForkJoin",
        "src/modalities/fork_join.rs",
        "        matches!(self.phase, ForkJoinPhase::Done)\n",
        "        !matches!(self.phase, ForkJoinPhase::Done)\n",
        "Requires DoneStuttering to report exactly the Done phase without changing state.",
        formal_module="formal/execution/carriers/ForkJoin.tla",
        executable_carrier="ForkJoin",
        carried_obligation="DoneStuttering guard and stutter relation",
        affected_action="done_stuttering / DoneStuttering",
        expected_fault="The terminal observation reports the negation of the Done guard.",
        anchor_start="    pub fn done_stuttering(&mut self) -> (enabled: bool)",
        anchor_end="}\n\n}",
    ),
    Mutation(
        "propagation-pass-snapshot-locality",
        "PropagationPass",
        "src/primitives/propagation_pass.rs",
        "        let next = self.combine_node(n);",
        "        let next = self.snapshot[n];",
        "Requires each update to apply the declared combine operation to the round snapshot.",
        formal_module="formal/structures/PropagationPass/PropagationPassGraph.tla",
        executable_carrier="PropagationPass",
        carried_obligation="SnapshotLocality",
        affected_action="update_node / UpdateNode",
        expected_fault="A node update bypasses the declared snapshot combine operation.",
    ),
    Mutation(
        "propagation-pass-iteration-bound",
        "PropagationPass",
        "src/primitives/propagation_pass.rs",
        "        self.iteration = self.iteration + 1;\n",
        "        self.iteration = self.max_iterations + 1;\n",
        "Requires EndRound to advance once without crossing the declared iteration ceiling.",
        formal_module="formal/structures/PropagationPass/PropagationPassGraph.tla",
        executable_carrier="PropagationPass",
        carried_obligation="IterationBound through EndRound",
        affected_action="end_round / EndRound",
        expected_fault="The round commit records an iteration above MaxIterations.",
    ),
    Mutation(
        "sequential-begin-activation",
        "Sequential",
        "src/modalities/sequential.rs",
        "            self.active = true;\n",
        "",
        "Requires BeginStep to activate the current sequential position.",
        formal_module="formal/execution/carriers/Sequential.tla",
        executable_carrier="Sequential",
        carried_obligation="BeginStep action relation and history-position agreement",
        affected_action="begin_step / BeginStep",
        expected_fault="BeginStep reports acceptance while the step remains inactive.",
    ),
    Mutation(
        "sequential-faulty-completion",
        "Sequential",
        "src/modalities/sequential.rs",
        "            self.history.push(next_value);\n",
        "",
        "Requires completion to append the produced value to sequential history.",
        formal_module="formal/execution/carriers/Sequential.tla",
        executable_carrier="Sequential",
        carried_obligation="HistoryPositionAgreement",
        affected_action="complete_step / CompleteStep",
        expected_fault="The cursor advances without the matching ordered history entry.",
    ),
    Mutation(
        "sequential-done-observation",
        "Sequential",
        "src/modalities/sequential.rs",
        "        self.pc == self.steps && !self.active\n",
        "        false\n",
        "Requires DoneStuttering to report exactly the terminal inactive state.",
        formal_module="formal/execution/carriers/Sequential.tla",
        executable_carrier="Sequential",
        carried_obligation="DoneStuttering guard and stutter relation",
        affected_action="done_stuttering / DoneStuttering",
        expected_fault="The terminal observation always rejects an enabled done state.",
    ),
    Mutation(
        "step-graph-backward-state",
        "StepGraph",
        "src/modalities/step_graph.rs",
        "            self.nstate.set(node, StepGraphNodeState::Complete);\n",
        "            self.nstate.set(node, StepGraphNodeState::NotReady);\n",
        "Requires completion to advance rather than move a node back to NotReady.",
        formal_module="formal/execution/carriers/StepGraph.tla",
        executable_carrier="StepGraph",
        carried_obligation="ProgressMonotonic",
        affected_action="complete_node / CompleteNode",
        expected_fault="Completion moves a node backward to NotReady.",
    ),
    Mutation(
        "step-graph-predecessor-bypass",
        "StepGraph",
        "src/modalities/step_graph.rs",
        "            && self.predecessors_complete_exec(node)\n",
        "",
        "Requires readiness to preserve the predecessor-completion guard.",
        formal_module="formal/execution/carriers/StepGraph.tla",
        executable_carrier="StepGraph",
        carried_obligation="EligibilityClosed; NoRunBeforePredecessors is derived",
        affected_action="become_ready / BecomeReady",
        expected_fault="A node becomes ready before every predecessor completes.",
    ),
    Mutation(
        "step-graph-start-state",
        "StepGraph",
        "src/modalities/step_graph.rs",
        "            self.nstate.set(node, StepGraphNodeState::Running);\n",
        "",
        "Requires StartRunning to advance the selected ready node to Running.",
        formal_module="formal/execution/carriers/StepGraph.tla",
        executable_carrier="StepGraph",
        carried_obligation="StartRunning action relation and progress monotonicity",
        affected_action="start_running / StartRunning",
        expected_fault="StartRunning reports acceptance while the node remains Ready.",
    ),
    Mutation(
        "step-graph-done-observation",
        "StepGraph",
        "src/modalities/step_graph.rs",
        "        true\n",
        "        false\n",
        "Requires DoneStuttering to accept after every node is Complete.",
        formal_module="formal/execution/carriers/StepGraph.tla",
        executable_carrier="StepGraph",
        carried_obligation="DoneStuttering guard and stutter relation",
        affected_action="done_stuttering / DoneStuttering",
        expected_fault="The terminal scan rejects even when every node is complete.",
        anchor_start="    pub fn done_stuttering(&mut self) -> (enabled: bool)",
        anchor_end="}\n\n}",
    ),
    Mutation(
        "stream-graph-drop-record",
        "StreamGraph",
        "src/modalities/stream_graph.rs",
        "            let _pushed = self.q2.push(value);\n",
        "",
        "Requires the middle operator to forward every removed record.",
        formal_module="formal/execution/carriers/StreamGraph.tla",
        executable_carrier="StreamGraph",
        carried_obligation="OccupancyCountConservation",
        affected_action="middle2_fire / Middle2Fire",
        expected_fault="A removed queue record is not forwarded.",
    ),
    Mutation(
        "stream-graph-third-stage-forward",
        "StreamGraph",
        "src/modalities/stream_graph.rs",
        "            let _pushed = self.q3.push(value);\n",
        "",
        "Requires Middle3Fire to forward the removed record to the third edge.",
        formal_module="formal/execution/carriers/StreamGraph.tla",
        executable_carrier="StreamGraph",
        carried_obligation="OccupancyCountConservation through Middle3Fire",
        affected_action="middle3_fire / Middle3Fire",
        expected_fault="The optional fourth-stage relay removes a record without forwarding it.",
    ),
    Mutation(
        "stream-graph-sink-emission",
        "StreamGraph",
        "src/modalities/stream_graph.rs",
        "                let _popped = self.q2.pop();\n                let _counted = self.emitted.try_increment();\n",
        "                let _popped = self.q2.pop();\n                let _counted = true;\n",
        "Requires SinkConsume to pair a removed terminal record with an emission credit.",
        formal_module="formal/execution/carriers/StreamGraph.tla",
        executable_carrier="StreamGraph",
        carried_obligation="OccupancyCountConservation through SinkConsume",
        affected_action="sink_consume / SinkConsume",
        expected_fault="The sink removes a record without incrementing the emitted count.",
    ),
    Mutation(
        "stream-graph-done-observation",
        "StreamGraph",
        "src/modalities/stream_graph.rs",
        "        self.ingested.value() == self.max_inputs as u64\n",
        "        self.ingested.value() != self.max_inputs as u64\n",
        "Requires DoneStuttering to use the exact bounded-input completion guard.",
        formal_module="formal/execution/carriers/StreamGraph.tla",
        executable_carrier="StreamGraph",
        carried_obligation="DoneStuttering guard and stutter relation",
        affected_action="done_stuttering / DoneStuttering",
        expected_fault="The terminal observation inverts the bounded-input condition.",
        anchor_start="    pub fn done_stuttering(&mut self) -> (enabled: bool)",
        anchor_end="}\n\n}",
    ),
    Mutation(
        "stream-graph-fanout-drop-branch",
        "StreamGraphFanout",
        "src/modalities/stream_graph_fanout.rs",
        "            let _right_pushed = self.right_queue.push(value);\n",
        "",
        "Requires fan-out to commit the right-branch copy.",
        formal_module="formal/execution/carriers/StreamGraphFanout.tla",
        executable_carrier="StreamGraphFanout",
        carried_obligation="PerBranchConservation",
        affected_action="source_ingest / Broadcast",
        expected_fault="Fan-out drops the right-branch copy.",
    ),
    Mutation(
        "stream-graph-fanout-backpressure",
        "StreamGraphFanout",
        "src/modalities/stream_graph_fanout.rs",
        "            && self.right_queue.len() < self.right_queue.capacity\n",
        "",
        "Requires broadcast admission to check capacity on both output branches.",
        formal_module="formal/execution/carriers/StreamGraphFanout.tla",
        executable_carrier="StreamGraphFanout",
        carried_obligation="BackpressureCorrect",
        affected_action="source_ingest / Broadcast",
        expected_fault="Broadcast may overfill the right branch while the left branch still has room.",
    ),
    Mutation(
        "stream-graph-over-capacity",
        "StreamGraph",
        "src/modalities/stream_graph.rs",
        "            && self.q1.len() < self.q1.capacity\n",
        "",
        "Requires source admission to preserve the first queue's capacity guard.",
        formal_module="formal/execution/carriers/StreamGraph.tla",
        executable_carrier="StreamGraph",
        carried_obligation="BackpressureCorrect",
        affected_action="source_ingest / SourceIngest",
        expected_fault="Source admission can exceed the first queue capacity.",
    ),
    Mutation(
        "allocation-snapshot-cost-accounting",
        "AllocationSnapshot",
        "src/compositions/allocation_snapshot.rs",
        "        let _accepted = self.budget.try_allocate(node_cost);\n",
        "        let _accepted = true;\n",
        "Requires node admission to add the accepted node cost to the snapshot total.",
        formal_module="formal/structures/AllocationSnapshot/AllocationSnapshot.tla",
        executable_carrier="AllocationSnapshot",
        carried_obligation="BudgetConsistency and the AcceptNode cost relation",
        affected_action="accept_node / AcceptNode",
        expected_fault="Accepted membership advances without matching total-cost accounting.",
    ),
    Mutation(
        "allocation-snapshot-capture-fold",
        "AllocationSnapshot",
        "src/compositions/allocation_snapshot.rs",
        "        if n < num_nodes && 1 <= c && c <= available && !s.contains_exec(n) {\n",
        "        if false && n < num_nodes && 1 <= c && c <= available && !s.contains_exec(n) {\n",
        "Requires capture to equal the complete ordered fold of every supplied request through AcceptNode.",
        formal_module="formal/structures/AllocationSnapshot/AllocationSnapshot.tla",
        executable_carrier="AllocationSnapshot capture realization",
        carried_obligation="Exact guarded AcceptNode fold",
        affected_action="capture / repeated AcceptNode",
        expected_fault="The batch constructor silently skips every otherwise admissible request.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "audit-sink-last-hash",
        "AuditSink",
        "src/primitives/audit_sink.rs",
        "        self.last_hash = new_hash;\n",
        "",
        "Requires an append to install the stored record hash as last_hash.",
        formal_module="formal/structures/AuditSink/AuditSink.tla",
        executable_carrier="AuditSink",
        carried_obligation="HashConsistency and ChainIntegrity",
        affected_action="record / Record",
        expected_fault="The log advances while last_hash remains stale.",
    ),
    Mutation(
        "audit-sink-content-binding",
        "AuditSink",
        "src/primitives/audit_sink.rs",
        "            let entry = AuditEntry {\n                operation,\n",
        "            let entry = AuditEntry {\n                operation: 0,\n",
        "Requires the appended record content to match the operation used by the concrete hash.",
        formal_module="formal/structures/AuditSink/AuditSink.tla",
        executable_carrier="AuditSink",
        carried_obligation="HashBindsContent through Record",
        affected_action="record / Record",
        expected_fault="The stored operation differs from the content hashed into the record.",
    ),
    Mutation(
        "budget-allocation-credit",
        "Budget",
        "src/primitives/budget.rs",
        "            self.allocated = self.allocated + amount;\n",
        "",
        "Requires successful allocation to credit the allocated ledger term.",
        formal_module="formal/structures/Budget/Budget.tla",
        executable_carrier="Budget",
        carried_obligation="SafetyInvariant through the TryAllocate action relation",
        affected_action="try_allocate / TryAllocate",
        expected_fault="The method reports successful allocation without the specified ledger update.",
    ),
    Mutation(
        "budget-reservation-credit",
        "Budget",
        "src/primitives/budget.rs",
        "            self.reserved = self.reserved + amount;\n",
        "",
        "Requires successful reservation to credit the reserved ledger term.",
        formal_module="formal/structures/Budget/Budget.tla",
        executable_carrier="Budget",
        carried_obligation="SafetyInvariant through the Reserve action relation",
        affected_action="reserve / Reserve",
        expected_fault="The method reports successful reservation without the specified ledger update.",
    ),
    Mutation(
        "budget-reservation-commit-transfer",
        "Budget",
        "src/primitives/budget.rs",
        "        self.reserved = self.reserved - amount;\n",
        "",
        "Requires CommitReservation to debit the reservation while crediting allocation.",
        formal_module="formal/structures/Budget/Budget.tla",
        executable_carrier="Budget",
        carried_obligation="Ledger conservation through CommitReservation",
        affected_action="commit_reservation / CommitReservation",
        expected_fault="Committed capacity is credited without debiting the reservation ledger.",
    ),
    Mutation(
        "budget-release-debit",
        "Budget",
        "src/primitives/budget.rs",
        "        self.allocated = self.allocated - amount;\n",
        "",
        "Requires Release to debit the allocated ledger by the named amount.",
        formal_module="formal/structures/Budget/Budget.tla",
        executable_carrier="Budget",
        carried_obligation="Release action relation",
        affected_action="release / Release",
        expected_fault="Release returns without reducing allocated capacity.",
        anchor_start="    pub fn release(&mut self, amount: u64)",
        anchor_end="    // ── MarkEviction",
    ),
    Mutation(
        "budget-mark-eviction-credit",
        "Budget",
        "src/primitives/budget.rs",
        "        self.pending_eviction = self.pending_eviction + amount;\n",
        "",
        "Requires MarkEviction to credit pending eviction for the allocation debit.",
        formal_module="formal/structures/Budget/Budget.tla",
        executable_carrier="Budget",
        carried_obligation="Ledger conservation through MarkEviction",
        affected_action="mark_eviction / MarkEviction",
        expected_fault="Marked allocation is removed without entering the pending-eviction ledger.",
    ),
    Mutation(
        "budget-complete-eviction-debit",
        "Budget",
        "src/primitives/budget.rs",
        "        self.pending_eviction = self.pending_eviction - amount;\n",
        "",
        "Requires CompleteEviction to remove the named amount from pending eviction.",
        formal_module="formal/structures/Budget/Budget.tla",
        executable_carrier="Budget",
        carried_obligation="CompleteEviction action relation",
        affected_action="complete_eviction / CompleteEviction",
        expected_fault="Completed eviction leaves the pending-eviction ledger unchanged.",
    ),
    Mutation(
        "budget-facade-reservation-guard",
        "Budget",
        "src/api.rs",
        "        if amount <= self.inner.reserved {\n",
        "        if true {\n",
        "Requires the checked facade to reject a disabled reservation commit.",
        formal_module="formal/structures/Budget/Budget.tla",
        executable_carrier="Checked Budget facade",
        carried_obligation="CommitReservation enabling condition at the consumer boundary",
        affected_action="Budget::commit_reservation / CommitReservation",
        expected_fault="The public facade may invoke CommitReservation when amount exceeds reserved units.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "resource-registry-facade-remove-guard",
        "ResourceRegistry",
        "src/api.rs",
        "        let previous = self.inner.lookup(key);\n",
        "        let previous = Some(0);\n",
        "Requires the checked registry facade to call deregistration only for a present key.",
        formal_module="formal/structures/ResourceRegistry/ResourceRegistry.tla",
        executable_carrier="Checked ResourceRegistry facade",
        carried_obligation="Deregister enabling condition at the consumer boundary",
        affected_action="ResourceRegistry::remove / Deregister",
        expected_fault="The public facade may invoke Deregister for an absent key.",
        anchor_start="    pub fn remove(&mut self, key: u64)",
        anchor_end="    /// Read an entry by storage index",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "value-eq-u64-fidelity",
        "ResourceRegistry",
        "src/value_eq.rs",
        "        *self == *other\n",
        "        false\n",
        "Requires executable u64 key equality to agree with specification equality.",
        formal_module="formal/structures/ResourceRegistry/ResourceRegistry.tla",
        executable_carrier="ValueEq adapter used by ResourceRegistry and Buffer",
        carried_obligation="UniqueMapping key identity and retained buffer membership",
        affected_action="ValueEq::value_eq / key and membership comparison",
        expected_fault="Equal u64 values may be treated as distinct by executable carriers.",
        anchor_start="impl ValueEq for u64 {",
        anchor_end="impl ValueEq for usize {",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "propagation-facade-start-guard",
        "PropagationPass",
        "src/api.rs",
        "        if !self.inner.changed || self.inner.iteration >= self.inner.max_iterations {\n",
        "        if false {\n",
        "Requires the checked propagation facade to reject a settled or exhausted start.",
        formal_module="formal/structures/PropagationPass/PropagationPassGraph.tla",
        executable_carrier="Checked PropagationPass facade",
        carried_obligation="StartRound enabling condition at the consumer boundary",
        affected_action="PropagationPass::start_round / StartRound",
        expected_fault="The public facade may start a round after settlement or exhaustion.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "propagation-pass-start-commit",
        "PropagationPass",
        "src/primitives/propagation_pass.rs",
        "        self.round = Round::Running;\n",
        "",
        "Requires StartRound to commit the transition from Idle to Running.",
        formal_module="formal/structures/PropagationPass/PropagationPassGraph.tla",
        executable_carrier="PropagationPass",
        carried_obligation="StartRound action relation and snapshot phase ownership",
        affected_action="start_round / StartRound",
        expected_fault="StartRound refreshes auxiliary data without entering the running phase.",
    ),
    Mutation(
        "propagation-pass-terminate-stutter",
        "PropagationPass",
        "src/primitives/propagation_pass.rs",
        "    {\n    }\n",
        "    {\n        self.changed = !self.changed;\n    }\n",
        "Requires Terminate to be an exact enabled stutter.",
        formal_module="formal/structures/PropagationPass/PropagationPassGraph.tla",
        executable_carrier="PropagationPass",
        carried_obligation="Terminate action relation",
        affected_action="terminate / Terminate",
        expected_fault="Terminate changes the fixed-point flag instead of stuttering.",
        anchor_start="    pub fn terminate(&mut self)",
        anchor_end="}\n\nfn false_vector",
    ),
    Mutation(
        "actuation-facade-finish-guard",
        "ActuationPass",
        "src/api.rs",
        "        if !self.inner.ready_to_finish_exec() {\n",
        "        if false {\n",
        "Requires the checked actuation facade to reject incomplete closure.",
        formal_module="formal/structures/ActuationPass/ActuationPass.tla",
        executable_carrier="Checked ActuationPass facade",
        carried_obligation="Finish enabling condition at the consumer boundary",
        affected_action="ActuationPass::finish / Finish",
        expected_fault="The public facade may finish before every allocated seat is actuated.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "quality-hierarchy-facade-isolation-guard",
        "QualityHierarchy",
        "src/api.rs",
        "        if !self.inner.can_set_node_properties(node, level, cost) {\n",
        "        if false {\n",
        "Requires the checked hierarchy facade to restrict property updates to isolated nodes.",
        formal_module="formal/structures/QualityHierarchy/QualityHierarchy.tla",
        executable_carrier="Checked QualityHierarchy facade",
        carried_obligation="SetNodeProperties enabling condition at the consumer boundary",
        affected_action="QualityHierarchy::set_node_properties / SetNodeProperties",
        expected_fault="The public facade may change the level or cost of a node already retained in an edge.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "backtracking-facade-delta-guard",
        "BacktrackingTraversal",
        "src/api.rs",
        "        if delta < 1 || delta > 2 {\n",
        "        if false {\n",
        "Requires the checked traversal facade to admit only deltas with a defined inverse.",
        formal_module="formal/structures/BacktrackingTraversal/BacktrackingTraversalUndo.tla",
        executable_carrier="Checked BacktrackingTraversal facade",
        carried_obligation="Descend mutation-domain enabling condition at the consumer boundary",
        affected_action="BacktrackingTraversal::descend / Descend",
        expected_fault="The public facade may descend with a delta outside the paired do-undo domain.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "projection-membership-agreement",
        "Projection",
        "src/connectives/projection.rs",
        "    ensures !membership_consistent(projected, source),\n",
        "    ensures membership_consistent(projected, source),\n",
        "Requires projected membership to agree with its retained source.",
        formal_module="formal/structures/RelationshipGraph/RelationshipGraph.tla",
        executable_carrier="Projection connective in RelationshipGraph",
        carried_obligation="AdjacencyConsistency",
        affected_action="membership_consistent / graph projection",
        expected_fault="The adjacency view disagrees with the retained edge relation.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "cursor-admission-direction",
        "Cursor",
        "src/connectives/cursor.rs",
        "    ensures !cursor_admitted(position, head),\n",
        "    ensures cursor_admitted(position, head),\n",
        "Requires a retained cursor to remain at or before its admitted head.",
        formal_module="formal/structures/Bisection/Bisection.tla",
        executable_carrier="Cursor connective in Bisection",
        carried_obligation="monotone lower-bound movement",
        affected_action="cursor_admitted / ProbeLeft or ProbeRight",
        expected_fault="A forward or stuttering cursor step is classified as inadmissible.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "cursor-facade-regression-guard",
        "Cursor",
        "src/api.rs",
        "        if position < self.inner.position {\n",
        "        if false {\n",
        "Requires the checked Cursor facade to reject regression.",
        formal_module="formal/structures/Bisection/Bisection.tla",
        executable_carrier="Checked Cursor facade",
        carried_obligation="monotone cursor movement at the consumer boundary",
        affected_action="Cursor::advance_to / monotone movement",
        expected_fault="The public facade may invoke a cursor move below the retained position.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "cursor-position-commit",
        "Cursor",
        "src/connectives/cursor.rs",
        "        self.position = position;\n",
        "",
        "Requires AdvanceTo to commit the caller-supplied monotone position.",
        formal_module="formal/structures/Bisection/Bisection.tla",
        executable_carrier="Cursor connective",
        carried_obligation="Monotone cursor movement",
        affected_action="Cursor::advance_to / monotone movement",
        expected_fault="AdvanceTo returns while retaining the prior position.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "accumulator-partition-reconstruction",
        "Accumulator",
        "src/connectives/accumulator.rs",
        "    ensures !carries(complete, accumulated, pending),\n",
        "    ensures carries(complete, accumulated, pending),\n",
        "Requires accumulated and pending segments to reconstruct the complete sequence.",
        formal_module="formal/structures/Reduction/ReductionStream.tla",
        executable_carrier="Accumulator connective in Reduction",
        carried_obligation="ConsumedPrefixFold source partition",
        affected_action="carries / Process",
        expected_fault="The retained prefix and pending suffix no longer reconstruct the source.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "accumulator-advance-commit",
        "Accumulator",
        "src/connectives/accumulator.rs",
        "        self.accumulated.push(value);\n",
        "",
        "Requires Advance to move the pending head into the accumulated prefix.",
        formal_module="formal/structures/Reduction/ReductionStream.tla",
        executable_carrier="Accumulator connective",
        carried_obligation="Ordered pending-head transfer",
        affected_action="Accumulator::advance / Process",
        expected_fault="Advance removes a pending value without appending it to the accumulated prefix.",
        anchor_start="    pub fn advance(&mut self) -> (value: Option<T>)",
        anchor_end="    /// Append one value",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "accumulator-append-commit",
        "Accumulator",
        "src/connectives/accumulator.rs",
        "        self.accumulated.push(value);\n",
        "",
        "Requires Append to extend the accumulated prefix by exactly one value.",
        formal_module="formal/structures/Reduction/ReductionStream.tla",
        executable_carrier="Accumulator connective",
        carried_obligation="Append action relation",
        affected_action="Accumulator::append / append output",
        expected_fault="Append updates ghost reconstruction without committing the concrete value.",
        anchor_start="    pub fn append(&mut self, value: T)",
        anchor_end="}\n\n}",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "accumulator-prefix-observation",
        "Accumulator",
        "src/connectives/accumulator.rs",
        "        if index < self.accumulated.len() { Some(self.accumulated[index]) } else { None }\n",
        "        None\n",
        "Requires the accumulated-prefix observer to return the retained indexed value.",
        formal_module="formal/structures/Reduction/ReductionStream.tla",
        executable_carrier="Accumulator connective",
        carried_obligation="Accumulated-prefix observation",
        affected_action="Accumulator::accumulated / Process observation",
        expected_fault="A present accumulated value is reported as absent.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "accumulator-pending-observation",
        "Accumulator",
        "src/connectives/accumulator.rs",
        "        if index < self.pending.len() { Some(self.pending[index]) } else { None }\n",
        "        None\n",
        "Requires the pending-suffix observer to return the retained indexed value.",
        formal_module="formal/structures/Reduction/ReductionStream.tla",
        executable_carrier="Accumulator connective",
        carried_obligation="Pending-suffix observation",
        affected_action="Accumulator::pending / Process observation",
        expected_fault="A present pending value is reported as absent.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "marker-selected-set",
        "Marker",
        "src/connectives/marker.rs",
        "    ensures !set_if(before, false, true),\n",
        "    ensures set_if(before, false, true),\n",
        "Requires a selected marker transition to set its retained flag.",
        formal_module="formal/structures/ActuationPass/ActuationPass.tla",
        executable_carrier="Marker connective in ActuationPass",
        carried_obligation="Finish closure marker transition",
        affected_action="set_if / Finish",
        expected_fault="A selected closure transition may leave the completion marker unset.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "marker-set-commit",
        "Marker",
        "src/connectives/marker.rs",
        "        self.marked = true;\n",
        "",
        "Requires Marker::set to commit the set state and exact change result.",
        formal_module="formal/structures/ActuationPass/ActuationPass.tla",
        executable_carrier="Marker connective",
        carried_obligation="Selected marker set transition",
        affected_action="Marker::set / selected transition",
        expected_fault="Set reports a change while leaving the marker unchanged.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "marker-clear-commit",
        "Marker",
        "src/connectives/marker.rs",
        "        self.marked = false;\n",
        "",
        "Requires Marker::clear to commit the clear state and exact change result.",
        formal_module="formal/structures/ActuationPass/ActuationPass.tla",
        executable_carrier="Marker connective",
        carried_obligation="Selected marker clear transition",
        affected_action="Marker::clear / selected transition",
        expected_fault="Clear reports a change while leaving the marker set.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "counter-increment-progress",
        "Counter",
        "src/connectives/counter.rs",
        "    ensures !increment(pre, pre),\n",
        "    ensures increment(pre, pre),\n",
        "Requires one counted occurrence to advance progress by one.",
        formal_module="formal/structures/PropagationPass/PropagationPassGraph.tla",
        executable_carrier="Counter connective in PropagationPass",
        carried_obligation="IterationBound through EndRound",
        affected_action="increment / EndRound",
        expected_fault="A completed round does not advance the retained iteration count.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "counter-increment-commit",
        "Counter",
        "src/connectives/counter.rs",
        "        self.value = self.value + 1;\n",
        "",
        "Requires a successful increment to advance the retained count.",
        formal_module="formal/structures/PropagationPass/PropagationPassGraph.tla",
        executable_carrier="Counter connective",
        carried_obligation="Counted progress transition",
        affected_action="Counter::try_increment / counted progress",
        expected_fault="TryIncrement reports success without advancing the counter.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "counter-decrement-commit",
        "Counter",
        "src/connectives/counter.rs",
        "        self.value = self.value - 1;\n",
        "",
        "Requires a successful decrement to reduce the retained count.",
        formal_module="formal/structures/ResourceRegistry/ResourceRegistry.tla",
        executable_carrier="Counter connective",
        carried_obligation="Guarded decrement transition",
        affected_action="Counter::try_decrement / guarded decrement",
        expected_fault="TryDecrement reports success without reducing the counter.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "buffer-admitted-capacity",
        "Buffer",
        "src/connectives/buffer.rs",
        "    ensures buffer_bounded(values, capacity),\n",
        "    ensures !buffer_bounded(values, capacity),\n",
        "Requires a retained sequence at exact capacity to remain admitted.",
        formal_module="formal/execution/carriers/StreamGraph.tla",
        executable_carrier="Buffer connective in StreamGraph",
        carried_obligation="BackpressureCorrect",
        affected_action="buffer_bounded / SourceIngest and middle fire",
        expected_fault="A legal full buffer is excluded from the carrier invariant.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "buffer-push-commit",
        "Buffer",
        "src/connectives/buffer.rs",
        "        self.values.push(value);\n",
        "",
        "Requires an admitted Push to append the supplied value.",
        formal_module="formal/execution/carriers/StreamGraph.tla",
        executable_carrier="Buffer connective",
        carried_obligation="FIFO publish effect",
        affected_action="Buffer::push / source and relay publish",
        expected_fault="Push reports success without appending the supplied value.",
        anchor_start="    pub fn push(&mut self, value: T) -> (result: Result<(), T>)",
        anchor_end="    /// Remove and return the oldest retained value.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "buffer-pop-head",
        "Buffer",
        "src/connectives/buffer.rs",
        "        if self.values.is_empty() { None } else { Some(self.values.remove(0)) }\n",
        "        None\n",
        "Requires Pop to return and remove the oldest retained value.",
        formal_module="formal/execution/carriers/StreamGraph.tla",
        executable_carrier="Buffer connective",
        carried_obligation="FIFO receive effect",
        affected_action="Buffer::pop / relay and sink receive",
        expected_fault="Pop reports no value while leaving a nonempty FIFO unchanged.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "buffer-push-unique-commit",
        "Buffer",
        "src/connectives/buffer.rs",
        "        self.values.push(value);\n",
        "",
        "Requires PushUnique to append an admitted absent value.",
        formal_module="formal/structures/TraversalEngine/TraversalEngine.tla",
        executable_carrier="Buffer connective",
        carried_obligation="Distinct frontier admission",
        affected_action="Buffer::push_unique / frontier admission",
        expected_fault="PushUnique reports acceptance without extending the distinct frontier.",
        anchor_start="    pub fn push_unique(&mut self, value: T) -> (accepted: bool)",
        anchor_end="    /// Remove one distinct retained value",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "buffer-remove-value-commit",
        "Buffer",
        "src/connectives/buffer.rs",
        "                let _removed_value = self.values.remove(index);\n",
        "                let _removed_value = self.values.remove(0);\n",
        "Requires RemoveValue to delete the named position while preserving the order of every retained value.",
        formal_module="formal/structures/TraversalEngine/TraversalEngine.tla",
        executable_carrier="Buffer connective",
        carried_obligation="Exact order-preserving distinct frontier removal",
        affected_action="Buffer::remove_value / frontier removal",
        expected_fault="RemoveValue deletes the FIFO head instead of the position containing the named frontier value.",
        anchor_start="    pub fn remove_value(&mut self, value: T) -> (removed: bool)",
        anchor_end="}\n\n}",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "ordering-pass-first-selection",
        "OrderingPass",
        "src/connectives/ordering_pass.rs",
        "    ensures !selects_first(items, selected),\n",
        "    ensures selects_first(items, selected),\n",
        "Requires ordered consumption to select the first retained value.",
        formal_module="formal/structures/Reduction/ReductionStream.tla",
        executable_carrier="OrderingPass connective in Reduction",
        carried_obligation="ordered Process head selection",
        affected_action="selects_first / Process",
        expected_fault="Reduction may claim an item other than the retained head.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "resource-registry-install-replacement",
        "ResourceRegistry",
        "src/primitives/resource_registry.rs",
        "        self.entries.push((k, v));\n",
        "",
        "Requires register to install the provided replacement after removing old bindings.",
        formal_module="formal/structures/ResourceRegistry/ResourceRegistry.tla",
        executable_carrier="ResourceRegistry",
        carried_obligation="UniqueMapping through the complete Register action relation",
        affected_action="register / Register",
        expected_fault="Register removes the old binding but omits the new unique mapping.",
    ),
    Mutation(
        "resource-registry-removal-commit",
        "ResourceRegistry",
        "src/primitives/resource_registry.rs",
        "        self.entries = filtered;\n",
        "        let _ = filtered;\n",
        "Requires Deregister to install the sequence with the named key removed.",
        formal_module="formal/structures/ResourceRegistry/ResourceRegistry.tla",
        executable_carrier="ResourceRegistry",
        carried_obligation="UniqueMapping through the Deregister action relation",
        affected_action="deregister / Deregister",
        expected_fault="Deregister computes a filtered sequence but leaves the original registry live.",
        anchor_start="    pub fn deregister(&mut self, k: K)",
        anchor_end="}\n\n}",
    ),
    Mutation(
        "resource-registry-order-preserving-filter",
        "ResourceRegistry",
        "src/primitives/resource_registry.rs",
        "            let e = entries[i];\n",
        "            let e = entries[entries.len() - 1 - i];\n",
        "Requires the shared key-removal helper to preserve the relative order of every surviving binding.",
        formal_module="formal/structures/ResourceRegistry/ResourceRegistry.tla",
        executable_carrier="ResourceRegistry order-preserving filter",
        carried_obligation="Deterministic Register and Deregister storage effects",
        affected_action="without_key / Register and Deregister",
        expected_fault="Filtering scans the registry in reverse and reorders every surviving binding.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "governed-commit-evidence-coupling",
        "GovernedCommit",
        "src/integration/governed_commit.rs",
        "        self.evidence_persisted = true;\n",
        "",
        "Requires successful commit to persist evidence before entering Committed.",
        formal_module="formal/construction/governed-commit-bridge/tla/GovernedCommitExecutable.tla",
        executable_carrier="GovernedCommit",
        carried_obligation="abstract_commit_step and commit-evidence coupling",
        affected_action="commit_success / CommitSuccess",
        expected_fault="The carrier enters Committed without persisted evidence.",
        anchor_start="    pub fn commit_success(&mut self)",
        anchor_end="    pub fn recover(&mut self)",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "governed-commit-commit-owner-frame",
        "GovernedCommit",
        "src/integration/governed_commit.rs",
        "        let recorded = self.audit.record(0);\n",
        "        let recorded = self.audit.record(0);\n        self.registry.register(0, 0);\n",
        "Requires CommitSuccess to change only its named budget, attempt, actuation, audit, sequential, and phase effects.",
        formal_module="formal/construction/governed-commit-bridge/tla/GovernedCommitExecutable.tla",
        executable_carrier="GovernedCommit",
        carried_obligation="CommitSuccess untouched-registry frame",
        affected_action="commit_success / CommitSuccess",
        expected_fault="CommitSuccess silently rewrites the durable resource registry while persisting evidence.",
        anchor_start="    pub fn commit_success(&mut self)",
        anchor_end="    pub fn recover(&mut self)",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "governed-commit-resource-origin",
        "GovernedCommit",
        "src/integration/governed_commit.rs",
        "        registry.register(0, resource);\n",
        "        registry.register(0, 0);\n",
        "Requires construction to retain the caller-supplied resource in the durable registry and actuation owner.",
        formal_module="formal/construction/governed-commit-bridge/tla/GovernedCommitExecutable.tla",
        executable_carrier="GovernedCommit",
        carried_obligation="Exact executable Init origin",
        affected_action="GovernedCommit::new / Init",
        expected_fault="Construction replaces the caller-supplied resource with a constant registry value.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "governed-commit-crash-durable-frame",
        "GovernedCommit",
        "src/integration/governed_commit.rs",
        "        self.crashed = true;\n",
        "        self.budget = Budget::new(self.budget.capacity);\n        self.crashed = true;\n",
        "Requires crash to change only the volatile process flag and preserve every durable owner exactly.",
        formal_module="formal/construction/governed-commit-bridge/tla/GovernedCommitExecutable.tla",
        executable_carrier="GovernedCommit",
        carried_obligation="Crash durable-state frame",
        affected_action="crash / Crash",
        expected_fault="Crash silently clears the durable budget ledger before setting the volatile flag.",
        anchor_start="    pub fn crash(&mut self)",
        anchor_end="    /// Restart the volatile process state without changing durable owners.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "governed-commit-restart-durable-frame",
        "GovernedCommit",
        "src/integration/governed_commit.rs",
        "        self.crashed = false;\n",
        "        self.budget = Budget::new(self.budget.capacity);\n        self.crashed = false;\n",
        "Requires restart to clear only the volatile process flag and preserve every durable owner exactly.",
        formal_module="formal/construction/governed-commit-bridge/tla/GovernedCommitExecutable.tla",
        executable_carrier="GovernedCommit",
        carried_obligation="Restart durable-state frame",
        affected_action="restart / Restart",
        expected_fault="Restart silently clears the durable budget ledger while clearing the volatile flag.",
        anchor_start="    pub fn restart(&mut self)",
        anchor_end="}\n\n}",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "backtracking-state-restoration",
        "BacktrackingTraversal",
        "src/primitives/backtracking_traversal.rs",
        "        self.aux = restored;\n",
        "",
        "Requires ascent to restore the saved auxiliary value.",
        formal_module="formal/structures/BacktrackingTraversal/BacktrackingTraversalUndo.tla",
        executable_carrier="BacktrackingTraversal",
        carried_obligation="StateRestoration",
        affected_action="ascend / Ascend",
        expected_fault="Ascent consumes the undo token without restoring auxiliary state.",
    ),
    Mutation(
        "backtracking-path-ledger-pairing",
        "BacktrackingTraversal",
        "src/primitives/backtracking_traversal.rs",
        "        self.ledger.push(token);\n",
        "",
        "Requires descent to append the undo token paired with the new path element.",
        formal_module="formal/structures/BacktrackingTraversal/BacktrackingTraversalUndo.tla",
        executable_carrier="BacktrackingTraversal",
        carried_obligation="Pairing through Descend",
        affected_action="descend / Descend",
        expected_fault="The path advances without its matching undo token.",
    ),
    Mutation(
        "backtracking-leaf-record",
        "BacktrackingTraversal",
        "src/primitives/backtracking_traversal.rs",
        "        self.visited.push(copy);\n",
        "",
        "Requires Visit to record the fresh full-depth path.",
        formal_module="formal/structures/BacktrackingTraversal/BacktrackingTraversalUndo.tla",
        executable_carrier="BacktrackingTraversal",
        carried_obligation="Visit action relation and full-depth record effect",
        affected_action="visit / Visit",
        expected_fault="Visit returns without recording the current valid leaf.",
    ),
    Mutation(
        "convergence-governor-state-transition",
        "ConvergenceGovernor",
        "src/primitives/convergence_governor_phase_aware.rs",
        "        self.state = new_state;\n",
        "",
        "Requires update to commit the verified next governor state.",
        formal_module="formal/structures/ConvergenceGovernor/ConvergenceGovernorPhaseAware.tla",
        executable_carrier="ConvergenceGovernor",
        carried_obligation="ValidTransitionsProp and ConvergenceRequiresHistory",
        affected_action="update / Update",
        expected_fault="History and phase advance while the governor state remains stale.",
    ),
    Mutation(
        "convergence-governor-cold-cooling",
        "ConvergenceGovernor",
        "src/primitives/convergence_governor_phase_aware.rs",
        "        self.state = new_state;\n",
        "        self.state = GovState::Cooling;\n",
        "Requires the update transition to exclude cooling directly from a cold state.",
        formal_module="formal/structures/ConvergenceGovernor/ConvergenceGovernorPhaseAware.tla",
        executable_carrier="ConvergenceGovernor",
        carried_obligation="NoCoolingFromCold",
        affected_action="update / Update",
        expected_fault="An update may enter Cooling without the required prior active history.",
    ),
    Mutation(
        "equivalence-class-root-link",
        "EquivalenceClass",
        "src/compositions/equivalence_class.rs",
        "        self.parents.register(lower, higher);\n",
        "",
        "Requires an unequal-rank union to attach the lower-rank root to the higher-rank root.",
        formal_module="formal/structures/EquivalenceClass/EquivalenceClass.tla",
        executable_carrier="EquivalenceClass",
        carried_obligation="RepresentativeRootedness and RepresentativeIdempotence",
        affected_action="merge / Union",
        expected_fault="A reported successful union leaves the selected roots disconnected.",
        anchor_start="    fn attach_lower(&mut self, lower: usize, higher: usize)",
        anchor_end="    /// Attach equal-rank roots",
    ),
    Mutation(
        "equivalence-class-root-link-direction",
        "EquivalenceClass",
        "src/compositions/equivalence_class.rs",
        "        self.parents.register(lower, higher);\n",
        "        self.parents.register(higher, lower);\n",
        "Requires an unequal-rank union link to point from the lower-rank root to the higher-rank root.",
        formal_module="formal/structures/EquivalenceClass/EquivalenceClass.tla",
        executable_carrier="EquivalenceClass",
        carried_obligation="RankMonotonicity for the stored parent direction",
        affected_action="attach_lower / Union",
        expected_fault="The higher-rank root points backward to the lower-rank root.",
        anchor_start="    fn attach_lower(&mut self, lower: usize, higher: usize)",
        anchor_end="    /// Attach equal-rank roots",
    ),
    Mutation(
        "equivalence-class-equal-rank-root-link",
        "EquivalenceClass",
        "src/compositions/equivalence_class.rs",
        "        self.parents.register(lower, higher);\n",
        "",
        "Requires an equal-rank union to attach the selected lower root to the selected higher root.",
        formal_module="formal/structures/EquivalenceClass/EquivalenceClass.tla",
        executable_carrier="EquivalenceClass",
        carried_obligation="RepresentativeRootedness and RepresentativeIdempotence",
        affected_action="attach_equal / Union",
        expected_fault="An equal-rank union raises a rank but leaves the selected roots disconnected.",
        anchor_start="    fn attach_equal(&mut self, lower: usize, higher: usize, rank: u64)",
        anchor_end="    /// Union two representatives",
    ),
    Mutation(
        "equivalence-class-union-left-lower-attachment",
        "EquivalenceClass",
        "src/compositions/equivalence_class.rs",
        "            self.attach_lower(left_root, right_root);\n",
        "",
        "Requires a successful left-lower unequal-rank union branch to perform its attachment.",
        formal_module="formal/structures/EquivalenceClass/EquivalenceClass.tla",
        executable_carrier="EquivalenceClass",
        carried_obligation="Successful Union establishes equivalence",
        affected_action="union / Union",
        expected_fault="The branch reports success and consumes budget without linking the selected roots.",
        anchor_start="    pub fn union(&mut self, left: usize, right: usize) -> (merged: bool)",
        anchor_end="    /// Whether two elements resolve to the same root",
    ),
    Mutation(
        "equivalence-class-union-right-lower-attachment",
        "EquivalenceClass",
        "src/compositions/equivalence_class.rs",
        "            self.attach_lower(right_root, left_root);\n",
        "",
        "Requires a successful right-lower unequal-rank union branch to perform its attachment.",
        formal_module="formal/structures/EquivalenceClass/EquivalenceClass.tla",
        executable_carrier="EquivalenceClass",
        carried_obligation="Successful Union establishes equivalence",
        affected_action="union / Union",
        expected_fault="The branch reports success and consumes budget without linking the selected roots.",
        anchor_start="    pub fn union(&mut self, left: usize, right: usize) -> (merged: bool)",
        anchor_end="    /// Whether two elements resolve to the same root",
    ),
    Mutation(
        "equivalence-class-union-equal-attachment",
        "EquivalenceClass",
        "src/compositions/equivalence_class.rs",
        "            self.attach_equal(right_root, left_root, left_rank);\n",
        "",
        "Requires a successful equal-rank union branch to perform its attachment and rank update.",
        formal_module="formal/structures/EquivalenceClass/EquivalenceClass.tla",
        executable_carrier="EquivalenceClass",
        carried_obligation="Successful Union establishes equivalence and preserves rank monotonicity",
        affected_action="union / Union",
        expected_fault="The branch reports success and consumes budget without linking the selected roots.",
        anchor_start="    pub fn union(&mut self, left: usize, right: usize) -> (merged: bool)",
        anchor_end="    /// Whether two elements resolve to the same root",
    ),
    Mutation(
        "equivalence-class-equal-rank-increment",
        "EquivalenceClass",
        "src/compositions/equivalence_class.rs",
        "        self.ranks.register(higher, rank + 1);\n",
        "",
        "Requires equal-rank union to increment the surviving root rank.",
        formal_module="formal/structures/EquivalenceClass/EquivalenceClass.tla",
        executable_carrier="EquivalenceClass",
        carried_obligation="RankMonotonicity through the equal-rank Union branch",
        affected_action="merge_equal / Union",
        expected_fault="Equal-rank roots are linked without making the parent rank strictly greater.",
    ),
    Mutation(
        "equivalence-class-union-enabled-result",
        "EquivalenceClass",
        "src/compositions/equivalence_class.rs",
        "        if self.budget.allocated >= self.budget.capacity {\n            return false;\n        }\n",
        "        if self.budget.allocated >= self.budget.capacity {\n            return true;\n        }\n",
        "Requires Union's result to equal the exact budget-headroom and distinct-class enabling condition.",
        formal_module="formal/structures/EquivalenceClass/EquivalenceClass.tla",
        executable_carrier="EquivalenceClass",
        carried_obligation="Exact Union result and rejection stutter",
        affected_action="union / Union",
        expected_fault="A capacity-rejected union reports success without changing the parent forest.",
        anchor_start="    pub fn union(&mut self, left: usize, right: usize) -> (merged: bool)",
        anchor_end="    /// Whether two elements resolve to the same root",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "equivalence-class-same-observation",
        "EquivalenceClass",
        "src/compositions/equivalence_class.rs",
        "            true\n",
        "            false\n",
        "Requires Same to report a shared reached root as equivalent.",
        formal_module="formal/structures/EquivalenceClass/EquivalenceClass.tla",
        executable_carrier="EquivalenceClass",
        carried_obligation="Class-membership observation",
        affected_action="same / equivalence observation",
        expected_fault="Two elements with the same reached root are reported as different.",
        anchor_start="    pub fn same(&self, left: usize, right: usize) -> (equivalent: bool)",
        anchor_end="}\n\n}",
    ),
    Mutation(
        "federated-budget-master-conservation",
        "FederatedBudget",
        "src/compositions/federated_budget.rs",
        "        let master_accepted = self.master.try_allocate(amount);\n",
        "        let master_accepted = true;\n",
        "Requires sub-pool delegation to advance master allocation by the same amount.",
        formal_module="formal/structures/FederatedBudget/FederatedBudget.tla",
        executable_carrier="FederatedBudget",
        carried_obligation="CapacityConservation and MasterCapacityBound",
        affected_action="allocate_sub_pool / AllocateSubPool",
        expected_fault="Delegated sub-pool capacity is omitted from master allocation.",
    ),
    Mutation(
        "federated-budget-subpool-ceiling",
        "FederatedBudget",
        "src/compositions/federated_budget.rs",
        "        pool.commit_reservation(amount);\n",
        "        pool.allocated = pool.capacity + 1;\n",
        "Requires consumption within one sub-pool to remain at or below its delegated capacity.",
        formal_module="formal/structures/FederatedBudget/FederatedBudget.tla",
        executable_carrier="FederatedBudget",
        carried_obligation="SubPoolCapacityBound",
        affected_action="allocate_from_sub_pool / AllocateFromSubPool",
        expected_fault="A successful sub-pool allocation records consumption above that pool's capacity.",
        anchor_start="    pub fn allocate_from_sub_pool(&mut self, name: usize, amount: u64)",
        anchor_end="    pub fn release_from_sub_pool",
    ),
    Mutation(
        "federated-budget-release-transfer",
        "FederatedBudget",
        "src/compositions/federated_budget.rs",
        "        let _reserved = pool.reserve(amount);\n",
        "        let _reserved = pool.reserve(0);\n",
        "Requires release to return consumed sub-pool capacity to reservation.",
        formal_module="formal/structures/FederatedBudget/FederatedBudget.tla",
        executable_carrier="FederatedBudget",
        carried_obligation="CapacityConservation through ReleaseFromSubPool",
        affected_action="release_from_sub_pool / ReleaseFromSubPool",
        expected_fault="Released allocation is not restored to the sub-pool reservation ledger.",
    ),
    Mutation(
        "federated-budget-selected-pool-frame",
        "FederatedBudget",
        "src/compositions/federated_budget.rs",
        "        self.sub_pools.set(name, pool);\n",
        "        self.sub_pools.set(0, pool);\n",
        "Requires an accepted sub-pool allocation to update exactly the named pool and frame every other pool.",
        formal_module="formal/structures/FederatedBudget/FederatedBudget.tla",
        executable_carrier="FederatedBudget",
        carried_obligation="AllocateFromSubPool selected-owner effect and untouched-pool frame",
        affected_action="allocate_from_sub_pool / AllocateFromSubPool",
        expected_fault="Consumption is committed to pool zero instead of the caller-named pool.",
        anchor_start="    pub fn allocate_from_sub_pool(&mut self, name: usize, amount: u64)",
        anchor_end="    /// Return consumed capacity",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "quality-hierarchy-parent-agreement",
        "QualityHierarchy",
        "src/primitives/quality_hierarchy.rs",
        "        self.parent.set(c, p);\n",
        "",
        "Requires edge admission to update the child's parent view.",
        formal_module="formal/structures/QualityHierarchy/QualityHierarchy.tla",
        executable_carrier="QualityHierarchy",
        carried_obligation="ParentEdgeAgreement",
        affected_action="add_child / AddChild",
        expected_fault="The edge view advances while the parent view remains stale.",
    ),
    Mutation(
        "quality-hierarchy-level-descent",
        "QualityHierarchy",
        "src/primitives/quality_hierarchy.rs",
        "        self.edges.push((p, c));\n",
        "        self.edges.push((p, c));\n        self.level.set(c, self.level[p]);\n",
        "Requires the admitted edge to preserve strict descent from parent level to child level.",
        formal_module="formal/structures/QualityHierarchy/QualityHierarchy.tla",
        executable_carrier="QualityHierarchy",
        carried_obligation="StrictLevelDescent",
        affected_action="add_child / AddChild",
        expected_fault="The child level is changed to equal its new parent's level.",
        anchor_start="    pub fn add_child(&mut self, p: usize, c: usize)",
        anchor_end="    pub fn set_node_properties",
    ),
    Mutation(
        "quality-hierarchy-cost-order",
        "QualityHierarchy",
        "src/primitives/quality_hierarchy.rs",
        "        self.edges.push((p, c));\n",
        "        self.edges.push((p, c));\n        self.cost.set(c, 0);\n",
        "Requires the admitted edge to preserve nondecreasing cost from parent to child.",
        formal_module="formal/structures/QualityHierarchy/QualityHierarchy.tla",
        executable_carrier="QualityHierarchy",
        carried_obligation="CostMonotonicity",
        affected_action="add_child / AddChild",
        expected_fault="The child cost may be rewritten below its new parent's cost.",
        anchor_start="    pub fn add_child(&mut self, p: usize, c: usize)",
        anchor_end="    pub fn set_node_properties",
    ),
    Mutation(
        "quality-hierarchy-property-commit",
        "QualityHierarchy",
        "src/primitives/quality_hierarchy.rs",
        "        self.cost.set(n, c);\n",
        "",
        "Requires SetNodeProperties to commit both caller-supplied node properties.",
        formal_module="formal/structures/QualityHierarchy/QualityHierarchy.tla",
        executable_carrier="QualityHierarchy",
        carried_obligation="SetNodeProperties action relation",
        affected_action="set_node_properties / SetNodeProperties",
        expected_fault="The level changes but the named node cost remains stale.",
    ),
    Mutation(
        "relationship-graph-adjacency-projection",
        "RelationshipGraph",
        "src/compositions/relationship_graph.rs",
        "        self.registry.register((source, target, weight), ());\n",
        "",
        "Requires a new weighted edge to update the adjacency projection.",
        formal_module="formal/structures/RelationshipGraph/RelationshipGraph.tla",
        executable_carrier="RelationshipGraph",
        carried_obligation="AdjacencyConsistency",
        affected_action="add_edge / AddEdge",
        expected_fault="The edge relation advances without its adjacency projection.",
    ),
    Mutation(
        "relationship-graph-self-loop",
        "RelationshipGraph",
        "src/compositions/relationship_graph.rs",
        "        self.registry.register((source, target, weight), ());\n",
        "        self.registry.register((source, source, weight), ());\n",
        "Requires AddEdge to preserve the selected irreflexive policy in both graph views.",
        formal_module="formal/structures/RelationshipGraph/RelationshipGraph.tla",
        executable_carrier="RelationshipGraph",
        carried_obligation="NoSelfLoops under the selected irreflexive policy",
        affected_action="add_edge / AddEdge",
        expected_fault="The admitted destination is replaced with the source in both graph views.",
        anchor_start="    pub fn add_edge(\n",
        anchor_end="    /// Remove every registered weight",
    ),
    Mutation(
        "relationship-graph-remove-pair",
        "RelationshipGraph",
        "src/compositions/relationship_graph.rs",
        "                let _removed = self.registry.deregister_at(index);\n",
        "                let _removed = (key, ());\n",
        "Requires RemoveEdge to delete every registered weight for the named pair.",
        formal_module="formal/structures/RelationshipGraph/RelationshipGraph.tla",
        executable_carrier="RelationshipGraph",
        carried_obligation="RemoveEdge action relation and adjacency consistency",
        affected_action="remove_edge / RemoveEdge",
        expected_fault="The removal loop observes a matching edge without deleting it.",
    ),
    Mutation(
        "sampler-selection-commit",
        "Sampler",
        "src/compositions/sampler.rs",
        "        self.actuation.actuate(item);\n",
        "",
        "Requires sample to record the admitted supported item.",
        formal_module="formal/structures/Sampler/Sampler.tla",
        executable_carrier="Sampler",
        carried_obligation="Sample action relation and admitted selection commit",
        affected_action="sample / Sample",
        expected_fault="Sample reports an admitted item without adding it to the selection.",
    ),
    Mutation(
        "sampler-sample-bound",
        "Sampler",
        "src/compositions/sampler.rs",
        "        let _accepted = self.budget.try_allocate(1);\n",
        "        let _accepted = self.budget.try_allocate(2);\n",
        "Requires one Sample action to add at most one item within the sample-size ceiling.",
        formal_module="formal/structures/Sampler/Sampler.tla",
        executable_carrier="Sampler",
        carried_obligation="BoundedSample",
        affected_action="sample / Sample",
        expected_fault="One admitted sample appends two entries and can cross the sample-size bound.",
    ),
    Mutation(
        "sampler-support-selection",
        "Sampler",
        "src/compositions/sampler.rs",
        "        self.actuation.actuate(item);\n",
        "        self.actuation.actuate(0);\n",
        "Requires Sample to append the supported item named by its admitted argument.",
        formal_module="formal/structures/Sampler/Sampler.tla",
        executable_carrier="Sampler",
        carried_obligation="SupportConsistency",
        affected_action="sample / Sample",
        expected_fault="The carrier may append an unrelated zero-probability item.",
    ),
    Mutation(
        "sampler-zero-support-removal",
        "Sampler",
        "src/compositions/sampler.rs",
        "            self.actuation.deallocate(item);\n",
        "",
        "Requires zero to remove the named live support allocation when the item is not selected.",
        formal_module="formal/structures/Sampler/Sampler.tla",
        executable_carrier="Sampler",
        carried_obligation="SupportConsistency through the Zero action relation",
        affected_action="zero / Zero",
        expected_fault="Zero reports success but leaves the named support allocation live.",
        anchor_start="    pub fn zero(&mut self, item: usize) -> (accepted: bool)",
        anchor_end="    /// Weighted rejection over caller-supplied proposal and entropy.",
    ),
    Mutation(
        "sampler-weighted-admission",
        "Sampler",
        "src/compositions/sampler.rs",
        "        if entropy >= weight || self.contains_exec(item) {\n",
        "        if self.contains_exec(item) {\n",
        "Requires a weighted draw to reject entropy outside the named item's support weight.",
        formal_module="formal/structures/Sampler/Sampler.tla",
        executable_carrier="Sampler",
        carried_obligation="Weighted draw admission relation",
        affected_action="draw_weighted / DrawWeighted",
        expected_fault="A weighted draw accepts an item whose proposal entropy is outside its support.",
    ),
    Mutation(
        "sampler-weighted-selection-commit",
        "Sampler",
        "src/compositions/sampler.rs",
        "        self.sample(item);\n",
        "",
        "Requires an admitted weighted draw to consume one budget credit and record the selected effect.",
        formal_module="formal/structures/Sampler/Sampler.tla",
        executable_carrier="Sampler",
        carried_obligation="BoundedSample and SupportConsistency through DrawWeighted",
        affected_action="draw_weighted / DrawWeighted",
        expected_fault="A weighted draw reports success without committing the selected item.",
        anchor_start="    pub fn draw_weighted(&mut self, item: usize, entropy: u64) -> (accepted: bool)",
        anchor_end="    /// Uniform-support admission over a caller-supplied proposal.",
    ),
    Mutation(
        "sampler-uniform-admission",
        "Sampler",
        "src/compositions/sampler.rs",
        "        if weight == 0 || self.contains_exec(item) {\n",
        "        if weight > 0 || self.contains_exec(item) {\n",
        "Requires a uniform draw to admit exactly positive, unselected support.",
        formal_module="formal/structures/Sampler/Sampler.tla",
        executable_carrier="Sampler",
        carried_obligation="Uniform draw admission relation",
        affected_action="draw_uniform / DrawUniform",
        expected_fault="A uniform draw rejects supported items and admits zero-support items.",
    ),
    Mutation(
        "sampler-uniform-selection-commit",
        "Sampler",
        "src/compositions/sampler.rs",
        "        self.sample(item);\n",
        "",
        "Requires an admitted uniform draw to consume one budget credit and record the selected effect.",
        formal_module="formal/structures/Sampler/Sampler.tla",
        executable_carrier="Sampler",
        carried_obligation="BoundedSample and SupportConsistency through DrawUniform",
        affected_action="draw_uniform / DrawUniform",
        expected_fault="A uniform draw reports success without committing the selected item.",
        anchor_start="    pub fn draw_uniform(&mut self, item: usize) -> (accepted: bool)",
        anchor_end="}\n\n}",
    ),
    Mutation(
        "traversal-engine-budget-charge",
        "TraversalEngine",
        "src/compositions/traversal_engine.rs",
        "        let accepted = self.budget.try_allocate(NODE_COST);\n",
        "        let accepted = true;\n",
        "Requires an accepted visit to deduct its fixed modeled cost.",
        formal_module="formal/structures/TraversalEngine/TraversalEngine.tla",
        executable_carrier="TraversalEngine",
        carried_obligation="AcceptedCostAccounting through the VisitNode action relation",
        affected_action="visit_node / VisitNode",
        expected_fault="A visit is accepted without the specified budget deduction.",
    ),
    Mutation(
        "traversal-engine-frontier-order",
        "TraversalEngine",
        "src/compositions/traversal_engine.rs",
        "                let queued = queue.push_unique(target);\n",
        "                let queued = queue.push_unique(num_nodes - 1 - target);\n",
        "Requires root expansion to enqueue star children in the exact deterministic node order.",
        formal_module="formal/structures/TraversalEngine/TraversalEngine.tla",
        executable_carrier="TraversalEngine",
        carried_obligation="Exact ordered frontier effect",
        affected_action="enqueue_star_children / VisitNode(root)",
        expected_fault="Root expansion reverses the admitted child identity at each frontier position.",
        anchor_start="    fn enqueue_star_children(\n",
        anchor_end="    /// Visit one queued node",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "rate-limit-window-count",
        "RateLimit",
        "src/compositions/rate_limit.rs",
        "        } else {\n            self.budget.try_allocate(1)\n",
        "        } else {\n            true\n",
        "Requires an in-window acquisition to advance the window count.",
        formal_module="formal/structures/RateLimit/RateLimit.tla",
        executable_carrier="RateLimit",
        carried_obligation="WindowCountBound through the TryAcquire action relation",
        affected_action="try_acquire / TryAcquire",
        expected_fault="Acquire reports success without recording the in-window event.",
    ),
    Mutation(
        "rate-limit-window-start-future",
        "RateLimit",
        "src/compositions/rate_limit.rs",
        "        self.clock = self.clock + 1;\n",
        "        self.clock = self.clock + 1;\n        self.window_start = self.max_clock;\n",
        "Requires Tick to preserve a window start that is not later than the modeled clock.",
        formal_module="formal/structures/RateLimit/RateLimit.tla",
        executable_carrier="RateLimit",
        carried_obligation="WindowStartNotFuture through Tick",
        affected_action="tick / Tick",
        expected_fault="Tick may move the window start beyond the new modeled clock.",
    ),
    Mutation(
        "reduction-prefix-fold",
        "Reduction",
        "src/compositions/reduction.rs",
        "        let accepted = self.audit.record(x);\n",
        "        let accepted = true;\n",
        "Requires process to fold the consumed head into the result.",
        formal_module="formal/structures/Reduction/ReductionStream.tla",
        executable_carrier="Reduction",
        carried_obligation="ConsumedPrefixFold",
        affected_action="process / Consume",
        expected_fault="The consumed prefix advances while the fold result remains stale.",
    ),
    Mutation(
        "signal-value-commit",
        "Signal",
        "src/compositions/signal.rs",
        "        let _accepted = self.audit.record(value);\n",
        "        let _accepted = true;\n",
        "Requires SetValue to append the named change through the AuditSink owner.",
        formal_module="formal/structures/Signal/Signal.tla",
        executable_carrier="Signal",
        carried_obligation="SetValue action relation and notification provenance",
        affected_action="set_value / SetValue",
        expected_fault="SetValue reports a change without appending the new signal value.",
    ),
    Mutation(
        "signal-append-history-frame",
        "Signal",
        "src/compositions/signal.rs",
        "        let _accepted = self.audit.record(value);\n",
        "        self.audit.log = Vec::new();\n        self.audit.last_hash = 0;\n        let _accepted = self.audit.record(value);\n",
        "Requires SetValue to append after every prior audit entry without rewriting or discarding history.",
        formal_module="formal/structures/Signal/Signal.tla",
        executable_carrier="Signal",
        carried_obligation="Append-only SetValue history frame",
        affected_action="set_value / SetValue",
        expected_fault="SetValue clears the retained audit chain before recording the new value.",
        anchor_start="    pub fn set_value(&mut self, value: u64)",
        anchor_end="    /// Advance one pending listener",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "signal-notification-partition",
        "Signal",
        "src/compositions/signal.rs",
        "        self.cursors.set(listener, advanced);\n",
        "",
        "Requires notification to move the listener into the notified partition.",
        formal_module="formal/structures/Signal/Signal.tla",
        executable_carrier="Signal",
        carried_obligation="NotificationProvenance through NotifyListener",
        affected_action="notify_listener / NotifyListener",
        expected_fault="A pending listener is removed without recording notification.",
    ),
    Mutation(
        "signal-pending-notified-overlap",
        "Signal",
        "src/compositions/signal.rs",
        "        advanced.advance_to(head);\n",
        "        advanced.advance_to(head - 1);\n",
        "Requires notification to remove a listener from pending before recording delivery.",
        formal_module="formal/structures/Signal/Signal.tla",
        executable_carrier="Signal",
        carried_obligation="PendingNotifiedDisjointness",
        affected_action="notify_listener / NotifyListener",
        expected_fault="A listener remains pending while also entering the notified set.",
    ),
    Mutation(
        "select-then-actuate-effect-record",
        "SelectThenActuate",
        "src/compositions/select_then_actuate.rs",
        "        self.actuation.actuate(seat);\n",
        "",
        "Requires actuation to record the effect for the selected seat.",
        formal_module="formal/composition/structure-compositions/SelectThenActuate.tla",
        executable_carrier="SelectThenActuate",
        carried_obligation="ActuationScope and composition invariant",
        affected_action="actuate / Actuate",
        expected_fault="Actuation returns after selection without recording the effect.",
    ),
    Mutation(
        "select-then-actuate-zero-score-origin",
        "SelectThenActuate",
        "src/compositions/select_then_actuate.rs",
        "            selections.push(CompetitiveSelectionHard::new(num_candidates));\n",
        "            let mut selection = CompetitiveSelectionHard::new(num_candidates);\n            selection.update_score(0, 1);\n            selections.push(selection);\n",
        "Requires construction to bind every seat-local candidate score to the zero-valued Init state.",
        formal_module="formal/composition/structure-compositions/SelectThenActuate.tla",
        executable_carrier="SelectThenActuate",
        carried_obligation="Exact composed Init origin",
        affected_action="SelectThenActuate::new / Init",
        expected_fault="Construction seeds a nonzero score into every seat owner.",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "select-then-actuate-winner-binding",
        "SelectThenActuate",
        "src/compositions/select_then_actuate.rs",
        "        self.actuation.allocate(seat, winner as u64);\n",
        "        self.actuation.allocate(seat, 0);\n",
        "Requires Evaluate to preserve the selected winner through the actuation allocation.",
        formal_module="formal/composition/structure-compositions/SelectThenActuate.tla",
        executable_carrier="SelectThenActuate",
        carried_obligation="AllocationAgreement and WinnerOptimality",
        affected_action="evaluate / Evaluate allocation handoff",
        expected_fault="The actuation allocation can differ from the selected winner.",
    ),
    Mutation(
        "select-then-actuate-seat-frame",
        "SelectThenActuate",
        "src/compositions/select_then_actuate.rs",
        "        self.selections.set(seat, selection);\n",
        "        self.selections.push(selection);\n",
        "Requires Evaluate to replace exactly the named selection owner and frame every other seat owner.",
        formal_module="formal/composition/structure-compositions/SelectThenActuate.tla",
        executable_carrier="SelectThenActuate",
        carried_obligation="Evaluate selected-seat effect and untouched-seat frame",
        affected_action="evaluate / Evaluate",
        expected_fault="Evaluate appends the computed owner instead of replacing exactly the named seat.",
        anchor_start="    pub fn evaluate(&mut self, seat: usize)",
        anchor_end="    /// Revise one unapplied seat",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "traversal-budget-cost-conservation",
        "TraversalBudgetComposition",
        "src/compositions/traversal_budget_composition.rs",
        "        self.traversal.visit_node(node);\n",
        "",
        "Requires an accepted visit to advance total cost with its budget deduction.",
        formal_module="formal/composition/structure-compositions/TraversalBudgetComposition.tla",
        executable_carrier="TraversalBudgetComposition",
        carried_obligation="CompositionInvariant and AcceptedSubsetVisited",
        affected_action="visit_node / VisitNode",
        expected_fault="Remaining budget decreases without the matching total-cost charge.",
        anchor_start="    pub fn visit_and_accept(&mut self, node: usize)",
        anchor_end="    /// The unaffordable branch",
    ),
    Mutation(
        "traversal-budget-visited-coupling",
        "TraversalBudgetComposition",
        "src/compositions/traversal_budget_composition.rs",
        "        self.traversal.visit_node(node);\n",
        "        self.traversal.visit_node(0);\n",
        "Requires an accepted node to be recorded in the visited set in the same commit.",
        formal_module="formal/composition/structure-compositions/TraversalBudgetComposition.tla",
        executable_carrier="TraversalBudgetComposition",
        carried_obligation="AcceptedSubsetVisited",
        affected_action="visit_and_accept / VisitAndAccept",
        expected_fault="A node is accepted and charged without being marked visited.",
        anchor_start="    pub fn visit_and_accept(&mut self, node: usize)",
        anchor_end="    /// The unaffordable branch",
    ),
    Mutation(
        "traversal-budget-unaffordable-exact-effect",
        "TraversalBudgetComposition",
        "src/compositions/traversal_budget_composition.rs",
        "        self.traversal.visit_node(node);\n",
        "        self.traversal.skip(node);\n",
        "Requires the unaffordable wrapper branch to mark the node visited while framing accepted and budget owners.",
        formal_module="formal/composition/structure-compositions/TraversalBudgetComposition.tla",
        executable_carrier="TraversalBudgetComposition",
        carried_obligation="Exact unaffordable VisitNode effect",
        affected_action="skip_unaffordable / VisitNode rejection branch",
        expected_fault="The wrapper removes the frontier node without recording the required visited marker.",
        anchor_start="    pub fn skip_unaffordable(&mut self, node: usize)",
        anchor_end="    /// Pure frontier removal",
        verification_root="src/lib.rs",
    ),
    Mutation(
        "traversal-engine-accepted-visited-coupling",
        "TraversalEngine",
        "src/compositions/traversal_engine.rs",
        "        self.visited.set(node, marker);\n",
        "",
        "Requires every accepted visit to include the node in the visited set.",
        formal_module="formal/structures/TraversalEngine/TraversalEngine.tla",
        executable_carrier="TraversalEngine",
        carried_obligation="AcceptedSubsetVisited",
        affected_action="visit_node / VisitNode",
        expected_fault="An affordable node is accepted without being recorded as visited.",
    ),
    Mutation(
        "traversal-engine-visited-count",
        "TraversalEngine",
        "src/compositions/traversal_engine.rs",
        "                count = count + 1;\n",
        "",
        "Requires VisitedCount to equal the number of set marker owners.",
        formal_module="formal/structures/TraversalEngine/TraversalEngine.tla",
        executable_carrier="TraversalEngine",
        carried_obligation="Visited-set cardinality projection",
        affected_action="visited_count / visited projection",
        expected_fault="The executable visited count ignores set marker owners.",
    ),
    Mutation(
        "traversal-engine-skip-removal",
        "TraversalEngine",
        "src/compositions/traversal_engine.rs",
        "        let removed = self.queue.remove_value(node);\n",
        "        let removed = true;\n",
        "Requires Skip to remove exactly the named frontier node without other effects.",
        formal_module="formal/structures/TraversalEngine/TraversalEngine.tla",
        executable_carrier="TraversalEngine",
        carried_obligation="Skip action relation",
        affected_action="skip / Skip",
        expected_fault="Skip reports success while retaining the named frontier node.",
        anchor_start="    pub fn skip(&mut self, node: usize)",
        anchor_end="    /// Enabled-at-empty traversal termination",
    ),
    Mutation(
        "traversal-engine-terminate-stutter",
        "TraversalEngine",
        "src/compositions/traversal_engine.rs",
        "    {\n    }\n",
        "    {\n        self.root = 0;\n    }\n",
        "Requires Terminate to be an exact enabled stutter.",
        formal_module="formal/structures/TraversalEngine/TraversalEngine.tla",
        executable_carrier="TraversalEngine",
        carried_obligation="Terminate action relation",
        affected_action="terminate / Terminate",
        expected_fault="Terminate rewrites the retained root instead of stuttering.",
        anchor_start="    pub fn terminate(&mut self)",
        anchor_end="}\n\n}",
    ),
)


ALK_SPEC_SUBJECT = "ALK-SPEC-1"
ALK_SPEC_VECTOR_SHA256 = "664709f770a4e6c704a00e0c02042fb2a06934ad927dfa51b9bcae27b0d1c608"
ALK_SPEC_EXECUTION_SHA256 = "6fad8f961230a5aea84319a29721a35a8ffe3f1d70e1a49e7c2727dff4dca05d"
ALK_SPEC_PROFILES = {
    "local-reference/at-commit": {
        "profile": "local-reference",
        "assurance_mode": "at-commit",
        "commit_owner": "builder",
    },
    "modular/at-commit": {
        "profile": "modular",
        "assurance_mode": "at-commit",
        "commit_owner": "builder",
    },
    "delegated/at-commit": {
        "profile": "delegated",
        "assurance_mode": "at-commit",
        "commit_owner": "external-owner",
    },
    "delegated/precommit": {
        "profile": "delegated",
        "assurance_mode": "precommit",
        "commit_owner": "external-owner",
    },
    "delegated/postcommit": {
        "profile": "delegated",
        "assurance_mode": "postcommit",
        "commit_owner": "external-owner",
    },
    "delegated/unavailable": {
        "profile": "delegated",
        "assurance_mode": "unavailable",
        "commit_owner": "external-owner",
    },
    "bounded-distributed/at-commit": {
        "profile": "bounded-distributed",
        "assurance_mode": "at-commit",
        "commit_owner": "cluster-owner",
    },
}
ALK_SPEC_PATHS = {
    "credential": "mediated",
    "direct-database": "excluded",
    "debug": "excluded",
    "shared-memory": "excluded",
    "administrative": "mediated",
    "recovery": "mediated",
    "external-service": "external",
}
ALK_SPEC_MODEL_DISTINCT = {
    "ALKReferenceLocal": 253,
    "ALKReferenceModular": 253,
    "ALKReferenceDelegatedAtCommit": 261,
    "ALKReferenceDelegatedPrecommit": 261,
    "ALKReferenceDelegatedPostcommit": 261,
    "ALKReferenceDelegatedUnavailable": 15,
    "ALKReferenceDistributed": 271,
}
ALK_SPEC_MODEL_VARIANTS = {
    "ALKReferenceLocal": "local-reference/at-commit",
    "ALKReferenceModular": "modular/at-commit",
    "ALKReferenceDelegatedAtCommit": "delegated/at-commit",
    "ALKReferenceDelegatedPrecommit": "delegated/precommit",
    "ALKReferenceDelegatedPostcommit": "delegated/postcommit",
    "ALKReferenceDelegatedUnavailable": "delegated/unavailable",
    "ALKReferenceDistributed": "bounded-distributed/at-commit",
}
ALK_SPEC_VECTOR_SUITES = {
    "local-reference/at-commit": ("local-reference", "at-commit", 16, 82),
    "modular/at-commit": ("modular", "at-commit", 16, 82),
    "delegated/at-commit": ("delegated", "at-commit", 17, 86),
    "delegated/precommit": ("delegated", "precommit", 17, 86),
    "delegated/postcommit": ("delegated", "postcommit", 17, 86),
    "delegated/unavailable": ("delegated", "unavailable", 5, 14),
    "bounded-distributed/at-commit": ("bounded-distributed", "at-commit", 18, 107),
}
ALK_SPEC_CONTROL_INVARIANTS = {
    "ControlExcludedPath": "PathUseClassified",
    "ControlEffectWithoutAdmission": "EffectAdmissionCoupled",
    "ControlCommitOwnerMismatch": "EffectOwnerCoupled",
    "ControlCommitWithoutEvidence": "CommitEvidenceCoupled",
    "ControlDuplicateEffect": "NoDuplicateEffect",
    "ControlStaleEpochCommit": "CurrentEpochAtCommit",
    "ControlRecoveryIntentLoss": "RecoveryIntentCoupled",
    "ControlLostResponseReplay": "RetryReplayIdempotent",
    "ControlOwnerVersionDrift": "OwnerRevisionBound",
    "ControlGuaranteeVersionDrift": "GuaranteeRevisionBound",
    "ControlTCBVersionDrift": "TCBRevisionBound",
    "ControlStaleCredentialAdmission": "FailSafeAdmissionHeld",
    "ControlPartitionCommit": "NoPartitionedCommit",
    "ControlDetachedRecovery": "RecoveryPathGoverned",
    "ControlEvidenceCustodyLoss": "EvidenceCustodyCoupled",
    "ControlSuccessWithoutEvidence": "SuccessCoupled",
    "ControlConfigurationEpochDrift": "ConfigurationEpochBound",
    "ControlMembershipDrift": "MembershipEpochBound",
    "ControlCredentialEpochDrift": "IdentityEpochBound",
    "ControlReorderedRequestEffect": "ReorderedRequestSafe",
    "ControlOwnerValueDrift": "OwnerConfigurationBound",
    "ControlGuaranteeValueDrift": "GuaranteeConfigurationBound",
    "ControlTCBValueDrift": "TCBConfigurationBound",
    "ControlTCBDependencyShrink": "TCBClosed",
    "ControlGuaranteeOverclaim": "GuaranteeWithinCeiling",
    "ControlConflictingDigestAlias": "ConflictingDigestSeparated",
    "ControlReorderedRequestNotOlder": "ReorderedRequestSafe",
    "ControlActionPathMismatch": "ActionPathBound",
    "ControlStaleReplayCurrentEpoch": "StaleReplayBound",
    "ControlProfileBridgeHiddenReconfiguration": "ProfileRelationBridgeBound",
    "ControlProfileBridgePartitionBeforeReconfiguration": "ProfileRelationBridgeBound",
    "ControlProfileBridgeCommitLabelAlias": "ProfileRelationBridgeBound",
}

IMPLEMENTATION_REFINEMENT_SUBJECTS = (
    "ActuationPass",
    "AllocationSnapshot",
    "AuditSink",
    "BacktrackingTraversal",
    "Bisection",
    "Budget",
    "CompetitiveSelection",
    "ConvergenceGovernor",
    "EquivalenceClass",
    "FederatedBudget",
    "ForkJoin",
    "PropagationPass",
    "QualityHierarchy",
    "RateLimit",
    "Reduction",
    "RelationshipGraph",
    "ResourceRegistry",
    "Sampler",
    "Sequential",
    "Signal",
    "StepGraph",
    "StreamGraph",
    "TraversalEngine",
)

EXECUTION_REFINEMENT_SUBJECTS = frozenset(
    {"Sequential", "ForkJoin", "StepGraph", "StreamGraph"}
)

IMPLEMENTATION_CONFORMANCE_FIELDS = (
    "initialization",
    "step-simulation",
    "observation-agreement",
    "commit-agreement",
    "failure-persistence-agreement",
    "rely-discharge",
    "liveness-preservation",
    "tcb-closure",
)

def repository_paths() -> tuple[Path, Path, Path | None]:
    configured = os.environ.get("AUTOMATION_STRUCTURE_ROOT")
    if configured:
        primary = Path(configured).resolve()
    elif DEFAULT_PRIMARY_CONTAINER.is_dir():
        primary = DEFAULT_PRIMARY_CONTAINER
    else:
        primary = Path(__file__).resolve().parents[1]
    repository = primary.parent
    supplementary = primary / "supplementary-research"
    return repository, primary, supplementary if supplementary.is_dir() else None


def relative_display(path: Path, root: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return path.as_posix()


def load_structure_purposes(primary: Path) -> dict[str, str]:
    candidates = [
        primary / "formal" / "construction" / "derivations" / "records",
        primary / "theory" / "derivations" / "records",
    ]
    records = next((path for path in candidates if path.is_dir()), None)
    purposes: dict[str, str] = {}
    if records is None:
        return purposes
    for path in sorted(records.glob("*.json")):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
            guarantees = data.get("guarantees", [])
            if guarantees:
                purposes[str(data["structure"])] = str(guarantees[0]["statement"])
        except (KeyError, TypeError, json.JSONDecodeError):
            continue
    return purposes


def classify_area(path: Path, scope_root: Path, scope: str) -> str:
    rel = path.relative_to(scope_root).as_posix().lower()
    if scope == "supplementary":
        parts = rel.split("/")
        if len(parts) > 1 and parts[0] == "studies":
            return parts[1]
        return parts[0]
    if rel.startswith("formal/structures/"):
        return "structures"
    if rel.startswith("formal/execution/"):
        return "execution"
    if rel.startswith("formal/composition/"):
        return "composition"
    if rel.startswith("formal/assurance/"):
        return "assurance"
    if "/alk/" in f"/{rel}" or rel.startswith("formal/construction/alk/"):
        return "alk"
    if rel.startswith("formal/construction/governed-commit-bridge/"):
        return "bridge"
    if "/derivations/" in f"/{rel}":
        return "derivations"
    if rel.startswith("formal/construction/"):
        return "construction"
    return rel.split("/", 1)[0]


def infer_subject(path: Path, scope_root: Path, area: str) -> str:
    rel = path.relative_to(scope_root)
    parts = rel.parts
    if area == "structures":
        for anchor in ("primitives", "structures"):
            if anchor in parts:
                index = parts.index(anchor)
                if index + 1 < len(parts):
                    name = parts[index + 1]
                    if name not in {"verus", "tools", "records", "theorems", "bridge", "witnesses"}:
                        return name
    stem = path.stem
    if "_NEG_" in stem:
        stem = stem.split("_NEG_", 1)[0]
    for suffix in ("_Proof", "_NEG"):
        if stem.endswith(suffix):
            stem = stem[: -len(suffix)]
    return stem


def infer_kind(path: Path, engine: str, expected: str) -> str:
    text = path.as_posix().lower()
    stem = path.stem.lower()
    if engine == "verus":
        return "implementation-proof"
    if engine == "rust":
        return "executable-check"
    if "distinctness" in text or "separation-witnesses" in text:
        return "separation-witness"
    if stem.endswith("_isolated"):
        return "control-baseline"
    if expected == "violation" or "control" in text or "_neg" in stem:
        return "control"
    if "refinement" in text or "refines" in stem:
        return "refinement"
    if "profile" in text:
        return "profile"
    if "spec" in text and "alk" in text:
        return "reference-specification"
    return "proof" if engine == "tlaps" else "model"


def infer_purpose(
    subject: str,
    kind: str,
    purposes: dict[str, str],
) -> str:
    if subject in purposes:
        return purposes[subject]
    descriptions = {
        "control": "Demonstrates that a named broken obligation or binding is rejected.",
        "control-baseline": "Checks the unmodified source under the same isolated obligation used by its paired control.",
        "separation-witness": "Produces a bounded trace that separates specified execution observations.",
        "refinement": "Checks a named abstraction or refinement relation under its recorded mapping.",
        "profile": "Checks a bounded ALK profile instance and its registered failure ceilings.",
        "reference-specification": "Checks the versioned ALK reference state machine and API behavior.",
        "implementation-proof": "Verifies the written Verus specifications for executable carriers.",
        "executable-check": "Runs deterministic known-answer vectors against compiled carriers.",
        "proof": "Discharges the theorems declared by this TLAPS module.",
        "model": "Explores the configured finite state space and checks its named properties.",
    }
    return descriptions[kind]


def expected_tlc_outcome(path: Path) -> str:
    rel = path.as_posix().lower()
    stem = path.stem.lower()
    if "distinctness" in rel or "separation-witnesses" in rel:
        return "violation"
    if "_neg" in stem and not stem.endswith("_isolated"):
        return "violation"
    if stem.endswith("_vio"):
        return "violation"
    if stem.endswith("decomposed") or stem.endswith("naive"):
        return "violation"
    return "success"


def config_directives(config: Path, directive: str) -> list[str]:
    pattern = re.compile(
        rf"^\s*{re.escape(directive)}\s+([A-Za-z][A-Za-z0-9_]*)\s*$",
        re.MULTILINE,
    )
    return pattern.findall(config.read_text(encoding="utf-8"))


def refinement_control_expected_failure(source: Path, config: Path) -> str | None:
    if source.parent.name != "refinement" or not source.stem.endswith("ImplRefinesSpec_NEG"):
        return None
    properties = config_directives(config, "PROPERTY")
    invariants = config_directives(config, "INVARIANT")
    if len(properties) != 1:
        raise RuntimeError(
            f"implementation-refinement control {config} must configure exactly one PROPERTY; "
            f"found {properties or 'none'}"
        )
    if not invariants:
        raise RuntimeError(
            f"implementation-refinement control {config} must configure adjacent INVARIANT checks"
        )
    return f"property:{properties[0]}"


def longest_module_prefix(stem: str, modules: set[str]) -> str | None:
    matches = [name for name in modules if stem == name or stem.startswith(name + "_")]
    return max(matches, key=len) if matches else None


def resolve_config_module(config: Path, modules: set[str]) -> str | None:
    stem = config.stem
    if stem in modules:
        return stem
    if stem.startswith("Control") and "ALKReferenceStateMachineControls" in modules:
        return "ALKReferenceStateMachineControls"
    if stem.startswith("ALKReference") and "ALKReferenceStateMachine" in modules:
        return "ALKReferenceStateMachine"
    return longest_module_prefix(stem.removesuffix("_isolated"), modules)


def nearest_path(anchor: Path, candidates: Sequence[Path]) -> Path:
    """Select the candidate with the shortest directory distance from anchor."""
    anchor_parts = anchor.parent.parts

    def rank(candidate: Path) -> tuple[int, str]:
        candidate_parts = candidate.parent.parts
        common = 0
        for left, right in zip(anchor_parts, candidate_parts):
            if left != right:
                break
            common += 1
        distance = len(anchor_parts) + len(candidate_parts) - 2 * common
        return distance, candidate.as_posix().lower()

    return min(candidates, key=rank)


def validate_proof_source_contract(root: Path, tla_files: Sequence[Path]) -> int:
    """Reject proof-source shapes that delegate unstable premise discovery."""
    offenders: list[str] = []
    by_clause = re.compile(
        r"\bBY\b(?P<body>.*?)"
        r"(?=^\s*(?:<\d+>|THEOREM\b|LEMMA\b|====)|\Z)",
        re.M | re.S,
    )
    for path in tla_files:
        try:
            source = strip_tla_comments(path.read_text(encoding="utf-8"))
        except ValueError as error:
            raise RuntimeError(f"cannot inspect TLA+ proof methods in {path}: {error}") from error
        source = re.sub(r'"(?:\\.|[^"\\])*"', '""', source)
        for line_number, line in enumerate(source.splitlines(), start=1):
            if re.search(r"\bIsa\b", line):
                offenders.append(
                    f"{path.relative_to(root).as_posix()}:{line_number}: explicit Isa"
                )
        for match in by_clause.finditer(source):
            tokens = set(re.findall(r"\b[A-Za-z][A-Za-z0-9_]*\b", match.group("body")))
            sequence_theorems = sorted(tokens & SEQUENCE_THEOREM_NAMES)
            if len(sequence_theorems) > 1:
                line_number = source.count("\n", 0, match.start()) + 1
                offenders.append(
                    f"{path.relative_to(root).as_posix()}:{line_number}: "
                    f"compound SequenceTheorems leaf "
                    f"{', '.join(sequence_theorems)}"
                )
    if offenders:
        raise RuntimeError(
            "unstable proof-source shapes are forbidden; use named, typed "
            "intermediate facts and no explicit Isabelle selection:\n  "
            + "\n  ".join(offenders)
        )
    return len(tla_files)


def discover_tla_items(
    scope: str,
    root: Path,
    purposes: dict[str, str],
) -> list[WorkItem]:
    def included(path: Path) -> bool:
        return not (scope == "primary" and "supplementary-research" in path.relative_to(root).parts)

    tla_files = [path for path in sorted(root.rglob("*.tla")) if included(path)]
    cfg_files = [path for path in sorted(root.rglob("*.cfg")) if included(path)]
    validate_proof_source_contract(root, tla_files)
    modules = {path.stem for path in tla_files}
    by_stem: dict[str, list[Path]] = {}
    for path in tla_files:
        by_stem.setdefault(path.stem, []).append(path)
    items: list[WorkItem] = []

    for proof in (path for path in tla_files if path.stem.endswith("_Proof")):
        area = classify_area(proof, root, scope)
        subject = infer_subject(proof, root, area)
        kind = infer_kind(proof, "tlaps", "success")
        item_id = f"{scope}:{area}:{subject}:tlaps:{proof.stem}"
        items.append(
            WorkItem(
                item_id,
                scope,
                area,
                subject,
                kind,
                "tlaps",
                proof,
                None,
                proof.stem,
                "success",
                infer_purpose(subject, kind, purposes),
            )
        )

    paired_negative_sources: set[Path] = set()
    missing_negative_pairs: list[str] = []
    for module_path in tla_files:
        match = re.match(r"^(?P<base>.+)_NEG_(?P<property>.+)$", module_path.stem)
        if not match:
            continue
        config_name = f"{match.group('base')}_{match.group('property')}_isolated.cfg"
        matches = [path for path in cfg_files if path.name == config_name]
        if not matches:
            missing_negative_pairs.append(
                f"{module_path.relative_to(root).as_posix()} requires {config_name}"
            )
            continue
        if len(matches) > 1:
            raise RuntimeError(
                f"ambiguous isolated configuration for {module_path}: "
                + ", ".join(str(path) for path in matches)
            )
        config = nearest_path(module_path, matches)
        paired_negative_sources.add(module_path)
        area = classify_area(module_path, root, scope)
        subject = infer_subject(module_path, root, area)
        kind = "control"
        item_id = f"{scope}:{area}:{subject}:tlc:{module_path.stem}"
        items.append(
            WorkItem(
                item_id,
                scope,
                area,
                subject,
                kind,
                "tlc",
                module_path,
                config,
                module_path.stem,
                "violation",
                infer_purpose(subject, kind, purposes),
            )
        )

    if missing_negative_pairs:
        raise RuntimeError(
            "unpaired negative TLA+ modules:\n  " + "\n  ".join(missing_negative_pairs)
        )

    negative_pair_names = {
        re.sub(r"_NEG_", "_", path.stem, count=1) + "_isolated.cfg"
        for path in tla_files
        if re.match(r"^.+_NEG_.+$", path.stem)
    }
    orphan_isolated = [
        path.relative_to(root).as_posix()
        for path in cfg_files
        if path.stem.endswith("_isolated") and path.name not in negative_pair_names
    ]
    if orphan_isolated:
        raise RuntimeError(
            "isolated configurations without matching negative modules:\n  "
            + "\n  ".join(orphan_isolated)
        )

    for config in cfg_files:
        module = resolve_config_module(config, modules)
        if module is None:
            considered = sorted(
                name
                for name in modules
                if name.lower() in config.stem.lower()
                or config.stem.lower() in name.lower()
                or name.startswith(config.stem.split("_")[0])
            )
            raise RuntimeError(
                "cannot resolve TLC configuration "
                f"{config.relative_to(root).as_posix()} to a TLA+ module; "
                "considered modules: "
                + (", ".join(considered) if considered else "none")
            )
        source = nearest_path(config, by_stem[module])
        if source in paired_negative_sources:
            continue
        expected = expected_tlc_outcome(config)
        area = classify_area(config, root, scope)
        subject = infer_subject(source, root, area)
        kind = infer_kind(config, "tlc", expected)
        qualifier = config.stem if config.stem != module else module
        item_id = f"{scope}:{area}:{subject}:tlc:{qualifier}"
        items.append(
            WorkItem(
                item_id,
                scope,
                area,
                subject,
                kind,
                "tlc",
                source,
                config,
                module,
                expected,
                infer_purpose(subject, kind, purposes),
                expected_failure=refinement_control_expected_failure(source, config),
            )
        )
    return items


def load_automation_structures_manifest(primary: Path) -> dict[str, str]:
    path = primary / AUTOMATION_STRUCTURES_MANIFEST
    try:
        manifest = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise RuntimeError(f"cannot read published-crate manifest {path}: {error}") from error
    required = {
        "crate",
        "version",
        "archive_sha256",
        "vcs_sha1",
        "download",
        "source_locator_prefix",
    }
    if not isinstance(manifest, dict) or set(manifest) != required:
        raise RuntimeError(
            "published-crate manifest must contain exactly: " + ", ".join(sorted(required))
        )
    if not all(isinstance(manifest[key], str) and manifest[key] for key in required):
        raise RuntimeError("published-crate manifest values must be nonempty strings")
    crate = manifest["crate"]
    version = manifest["version"]
    expected_download = (
        f"https://static.crates.io/crates/{crate}/{crate}-{version}.crate"
    )
    expected_prefix = f"crate://{crate}/{version}/"
    if manifest["download"] != expected_download:
        raise RuntimeError(
            "published-crate download does not match crate and version: "
            f"expected={expected_download}, observed={manifest['download']}"
        )
    if manifest["source_locator_prefix"] != expected_prefix:
        raise RuntimeError(
            "published-crate source locator does not match crate and version: "
            f"expected={expected_prefix}, observed={manifest['source_locator_prefix']}"
        )
    if re.fullmatch(r"[0-9a-f]{64}", manifest["archive_sha256"]) is None:
        raise RuntimeError("published-crate archive_sha256 must be lowercase SHA-256")
    if re.fullmatch(r"[0-9a-f]{40}", manifest["vcs_sha1"]) is None:
        raise RuntimeError("published-crate vcs_sha1 must be lowercase SHA-1")
    return manifest


def normalized_binding_digest(text: str) -> str:
    normalized = re.sub(r"\s+", " ", text).strip().encode("utf-8")
    return hashlib.sha256(normalized).hexdigest()


def require_binding_fragments(label: str, text: str, fragments: Iterable[str]) -> None:
    missing = [fragment for fragment in fragments if fragment not in text]
    if missing:
        raise ValueError(f"{label} missing semantic fragments {missing}")


def extract_verus_method_block(text: str, name: str) -> str:
    method = re.search(rf"(?m)^    pub\s+fn\s+{re.escape(name)}\s*\(", text)
    if method is None:
        raise ValueError(f"missing Rust method {name}")
    body_line = re.search(r"(?m)^    \{\s*$", text[method.end() :])
    if body_line is None:
        raise ValueError(f"missing Rust method body {name}")
    opening = method.end() + body_line.start() + body_line.group(0).index("{")
    depth = 0
    in_string = False
    escaped = False
    line_comment = False
    block_comment_depth = 0
    index = opening
    while index < len(text):
        char = text[index]
        following = text[index + 1] if index + 1 < len(text) else ""
        if line_comment:
            if char == "\n":
                line_comment = False
            index += 1
            continue
        if block_comment_depth:
            if char == "/" and following == "*":
                block_comment_depth += 1
                index += 2
                continue
            if char == "*" and following == "/":
                block_comment_depth -= 1
                index += 2
                continue
            index += 1
            continue
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == "/" and following == "/":
            line_comment = True
            index += 2
            continue
        if char == "/" and following == "*":
            block_comment_depth = 1
            index += 2
            continue
        if char == '"':
            in_string = True
        elif char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return text[method.start() : index + 1]
        index += 1
    raise ValueError(f"unclosed Rust method body {name}")


def extract_tla_action(text: str, name: str) -> str:
    action = re.search(rf"(?m)^{re.escape(name)}\s*==", text)
    if action is None:
        raise ValueError(f"missing TLA+ action {name}")
    following = text.find("\n\n", action.start())
    if following < 0:
        following = len(text)
    return text[action.start() : following]


def build_governed_commit_certificate(primary: Path, root: Path) -> dict[str, object]:
    manifest = load_automation_structures_manifest(primary)
    rust = root / "src" / "integration" / "governed_commit.rs"
    bridge_root = primary / "formal" / "construction" / "governed-commit-bridge"
    executable = bridge_root / "tla" / "GovernedCommitExecutable.tla"
    abstract = bridge_root / "tla" / "GovernedCommitAbstract.tla"
    proof = bridge_root / "tla" / "GovernedCommitBridge_Proof.tla"
    for path in (rust, executable, abstract, proof):
        if not path.is_file():
            raise ValueError(f"missing governed-commit identity source: {path}")

    rust_text = rust.read_text(encoding="utf-8")
    executable_text = executable.read_text(encoding="utf-8")
    require_binding_fragments(
        "integrated Rust roles", rust_text, GOVERNED_COMMIT_ROLE_BINDINGS
    )
    require_binding_fragments(
        "direct Verus refinement",
        rust_text,
        GOVERNED_COMMIT_DIRECT_REFINEMENT_FRAGMENTS,
    )
    if "external_body" in rust_text or re.search(r"\bassume\s*\(", rust_text):
        raise ValueError("claim-bearing Rust source contains an escape hatch")

    parser_probe = """    pub fn probe() -> (value: u64)
        ensures value == if true {
            1
        } else {
            0
        },
    {
        let body_marker = 1;
        body_marker
    }
"""
    probe_block = extract_verus_method_block(parser_probe, "probe")
    if "let body_marker = 1;" not in probe_block or not probe_block.rstrip().endswith("}"):
        raise ValueError("governed-commit method parser self-test failed")

    methods: dict[str, object] = {}
    for method, binding in GOVERNED_COMMIT_METHOD_BINDINGS.items():
        block = extract_verus_method_block(rust_text, method)
        require_binding_fragments(f"Rust method {method}", block, binding["rust"])
        action_digests: dict[str, str] = {}
        action_text = ""
        for action in binding["actions"]:
            extracted = extract_tla_action(executable_text, action)
            action_text += extracted
            action_digests[action] = normalized_binding_digest(extracted)
        require_binding_fragments(
            f"TLA actions for {method}", action_text, binding["tla"]
        )
        methods[method] = {
            "rust_contract_body_sha256": normalized_binding_digest(block),
            "tla_actions": list(binding["actions"]),
            "tla_action_sha256": action_digests,
        }

    proof_text = proof.read_text(encoding="utf-8")
    require_binding_fragments(
        "TLAPS certificate",
        proof_text,
        (
            "THEOREM InitializationRefinement",
            "THEOREM EveryExecutableStepRefines",
            "THEOREM ExactCommitPreimage",
            "THEOREM ExactFailurePreimage",
            "THEOREM ObservationAgreement",
            "THEOREM CommitAtomicityAndEvidence",
            "THEOREM GuaranteePreservation",
        ),
    )
    locator = manifest["source_locator_prefix"] + "src/integration/governed_commit.rs"
    return {
        "schema_version": 1,
        "translation_kind": "direct-verus-proof-and-cross-logic-identity-manifest",
        "semantic_refinement_logic": "Verus",
        "semantic_refinement_module": locator,
        "rust_source": locator,
        "rust_source_sha256": hashlib.sha256(rust.read_bytes()).hexdigest(),
        "abstract_relation": abstract.relative_to(primary).as_posix(),
        "abstract_relation_sha256": hashlib.sha256(abstract.read_bytes()).hexdigest(),
        "executable_relation": executable.relative_to(primary).as_posix(),
        "executable_relation_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
        "independent_tlaps_model_certificate": proof.relative_to(primary).as_posix(),
        "independent_tlaps_model_certificate_sha256": hashlib.sha256(
            proof.read_bytes()
        ).hexdigest(),
        "method_bindings": methods,
        "semantic_bridge_tcb": [
            "Verus Rust parser, verifier, bundled Z3, and source-level contract semantics",
        ],
        "cross_logic_model_identity_boundary": [
            "verification/run_proofs.py exact method-block parser and semantic binding table",
            "TLA+ SANY parser and TLAPS proof manager/backends for the independent finite mirror",
        ],
    }


def validate_governed_commit_certificate(primary: Path, root: Path) -> str:
    path = (
        primary
        / "formal"
        / "construction"
        / "governed-commit-bridge"
        / "TRANSLATION_CERTIFICATE.json"
    )
    try:
        observed = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"cannot read governed-commit certificate: {error}") from error
    expected = build_governed_commit_certificate(primary, root)
    if observed != expected:
        changed = sorted(
            key
            for key in set(observed if isinstance(observed, dict) else {}) | set(expected)
            if not isinstance(observed, dict) or observed.get(key) != expected.get(key)
        )
        raise ValueError(
            "governed-commit translation certificate is stale: "
            + ", ".join(changed)
        )
    action_count = sum(
        len(binding["actions"])
        for binding in GOVERNED_COMMIT_METHOD_BINDINGS.values()
    )
    return (
        "GOVERNED_COMMIT_IDENTITY|"
        f"methods={len(GOVERNED_COMMIT_METHOD_BINDINGS)}|actions={action_count}|"
        "parser-self-test=1|"
        f"rust-sha256={expected['rust_source_sha256']}"
    )


def find_verus_root(primary: Path) -> Path:
    manifest = load_automation_structures_manifest(primary)
    root = Path(
        os.environ.get(
            "AUTOMATION_STRUCTURES_CRATE_ROOT",
            str(DEFAULT_AUTOMATION_STRUCTURES_CRATE_ROOT),
        )
    ).resolve()
    required = (
        root / "Cargo.toml.orig",
        root / ".cargo_vcs_info.json",
        root / "src" / "lib.rs",
        root / "verification" / "run_verus_gate.sh",
    )
    missing = [path for path in required if not path.is_file()]
    if missing:
        raise RuntimeError(
            "published automation-structures source is absent from the verifier image: "
            + ", ".join(path.as_posix() for path in missing)
        )
    cargo = (root / "Cargo.toml.orig").read_text(encoding="utf-8")
    if re.search(r'^name\s*=\s*"automation-structures"\s*$', cargo, re.MULTILINE) is None:
        raise RuntimeError("published crate has the wrong package name")
    version_match = re.search(r'^version\s*=\s*"([^"]+)"\s*$', cargo, re.MULTILINE)
    if version_match is None or version_match.group(1) != manifest["version"]:
        observed = None if version_match is None else version_match.group(1)
        raise RuntimeError(
            f"published crate version mismatch: expected={manifest['version']}, observed={observed}"
        )
    try:
        vcs = json.loads((root / ".cargo_vcs_info.json").read_text(encoding="utf-8"))
        vcs_sha1 = vcs["git"]["sha1"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as error:
        raise RuntimeError(f"published crate has invalid VCS identity: {error}") from error
    if vcs_sha1 != manifest["vcs_sha1"]:
        raise RuntimeError(
            f"published crate VCS mismatch: expected={manifest['vcs_sha1']}, observed={vcs_sha1}"
        )
    return root


def resolve_source_locator(primary: Path, locator: str) -> Path:
    manifest = load_automation_structures_manifest(primary)
    prefix = manifest["source_locator_prefix"]
    if locator.startswith(prefix):
        suffix = locator.removeprefix(prefix)
        if not suffix or suffix.startswith("/") or ".." in Path(suffix).parts:
            raise ValueError(f"invalid published-crate source locator: {locator}")
        return find_verus_root(primary) / suffix
    return primary / locator


def validate_verus_mutation_registry(primary: Path, root: Path) -> None:
    registered_sources = {
        path.relative_to(root).as_posix()
        for path in (root / "src").rglob("*.rs")
        if path.name
        not in {
            "composition_api.rs",
            "connective_api.rs",
            "execution_api.rs",
            "lib.rs",
            "mod.rs",
            "verification.rs",
        }
    }
    if len(registered_sources) != 36:
        raise RuntimeError(
            f"expected 36 registered Verus source modules, found {len(registered_sources)}"
        )
    mutation_ids: set[str] = set()
    covered_sources: set[str] = set()
    errors: list[str] = []
    for mutation in VERUS_MUTATIONS:
        if mutation.id in mutation_ids:
            errors.append(f"duplicate mutation id: {mutation.id}")
        mutation_ids.add(mutation.id)
        covered_sources.add(mutation.source)
        if not all(
            (
                mutation.formal_module,
                mutation.executable_carrier,
                mutation.carried_obligation,
                mutation.affected_action,
                mutation.expected_fault,
            )
        ):
            errors.append(f"incomplete attribution fields: {mutation.id}")
        if not (primary / mutation.formal_module).is_file():
            errors.append(f"formal module does not exist: {mutation.id}: {mutation.formal_module}")
        source = root / mutation.source
        if not source.is_file():
            errors.append(f"Verus source does not exist: {mutation.id}: {mutation.source}")
            continue
        text = source.read_text(encoding="utf-8")
        if mutation.anchor_start is None:
            count = text.count(mutation.needle)
            if count != 1:
                errors.append(
                    f"mutation site is not unique: {mutation.id}: {count} matches"
                )
            continue
        if text.count(mutation.anchor_start) != 1:
            errors.append(
                f"mutation start anchor is not unique: {mutation.id}: "
                f"{text.count(mutation.anchor_start)} matches"
            )
            continue
        start = text.find(mutation.anchor_start)
        if mutation.anchor_end is None or text.count(mutation.anchor_end, start) != 1:
            count = 0 if mutation.anchor_end is None else text.count(mutation.anchor_end, start)
            errors.append(
                f"mutation end anchor is not unique after start: {mutation.id}: {count} matches"
            )
            continue
        end = text.find(mutation.anchor_end, start)
        count = text[start:end].count(mutation.needle)
        if count != 1:
            errors.append(
                f"anchored mutation site is not unique: {mutation.id}: {count} matches"
            )
    missing = sorted(registered_sources - covered_sources)
    extra = sorted(covered_sources - registered_sources)
    if missing:
        errors.append("registered Verus modules without a mutation: " + ", ".join(missing))
    if extra:
        errors.append("mutation sources outside the registered module inventory: " + ", ".join(extra))
    if errors:
        raise RuntimeError("invalid Verus mutation registry:\n  " + "\n  ".join(errors))


def validate_implementation_refinement_contract(primary: Path) -> str:
    record_root = primary / "formal" / "construction" / "derivations" / "records"
    formal_root = primary / "formal"
    structures_root = formal_root / "structures"
    execution_refinement_root = formal_root / "execution" / "carriers" / "refinement"
    errors: list[str] = []
    digest = hashlib.sha256()
    state_field_count = 0
    canonical_action_count = 0
    executable_action_count = 0
    source_check_count = 0
    expected_action_controls: set[tuple[str, str]] = set()
    observed_action_controls: set[tuple[str, str]] = set()
    action_control_link_count = 0
    verus_source_prefix = (
        load_automation_structures_manifest(primary)["source_locator_prefix"] + "src/"
    )

    action_control_path = primary / AUTOMATION_STRUCTURES_ACTION_CONTROLS
    try:
        action_control_registry = json.loads(action_control_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        errors.append(f"unreadable action-control registry: {error}")
        action_control_registry = {}
    if action_control_registry.get("schema_version") != 1:
        errors.append("action-control registry schema_version must be 1")
    action_controls = action_control_registry.get("actions")
    if not isinstance(action_controls, dict):
        errors.append("action-control registry actions must be an object")
        action_controls = {}
    mutation_by_id = {mutation.id: mutation for mutation in VERUS_MUTATIONS}
    for subject, methods in action_controls.items():
        if not isinstance(subject, str) or not subject or not isinstance(methods, dict):
            errors.append("action-control registry subject entries must map names to objects")
            continue
        for method, control_ids in methods.items():
            key = (subject, method)
            if key in observed_action_controls:
                errors.append(f"duplicate action-control entry: {subject}::{method}")
            observed_action_controls.add(key)
            if not isinstance(method, str) or not method or not isinstance(control_ids, list):
                errors.append(f"invalid action-control entry: {subject}::{method}")
                continue
            if not control_ids or not all(isinstance(value, str) and value for value in control_ids):
                errors.append(f"action-control entry has no control ids: {subject}::{method}")
                continue
            if len(control_ids) != len(set(control_ids)):
                errors.append(f"action-control entry repeats a control id: {subject}::{method}")
            action_control_link_count += len(control_ids)
            for control_id in control_ids:
                mutation = mutation_by_id.get(control_id)
                if mutation is None:
                    errors.append(
                        f"action-control entry names an unknown control: "
                        f"{subject}::{method}: {control_id}"
                    )
                elif mutation.subject != subject:
                    errors.append(
                        f"action-control subject mismatch: {subject}::{method}: "
                        f"{control_id} belongs to {mutation.subject}"
                    )
    if action_control_path.is_file():
        digest.update(action_control_path.relative_to(primary).as_posix().encode("utf-8"))
        digest.update(b"\0")
        digest.update(action_control_path.read_bytes())
        digest.update(b"\0")

    live_refinements = {
        path.stem.removesuffix("ImplRefinesSpec")
        for path in formal_root.rglob("*ImplRefinesSpec.tla")
        if not path.stem.endswith("_NEG")
    }
    expected_subjects = set(IMPLEMENTATION_REFINEMENT_SUBJECTS)
    if live_refinements != expected_subjects:
        errors.append(
            "implementation-refinement inventory mismatch: "
            f"expected={sorted(expected_subjects)!r}, observed={sorted(live_refinements)!r}"
        )

    for subject in IMPLEMENTATION_REFINEMENT_SUBJECTS:
        record_path = record_root / f"{subject}.json"
        if subject in EXECUTION_REFINEMENT_SUBJECTS:
            refinement_root = execution_refinement_root / subject
        else:
            refinement_root = structures_root / subject / "refinement"
        expected_files = (
            refinement_root / f"{subject}ImplRefinesSpec.tla",
            refinement_root / f"{subject}ImplRefinesSpec_Proof.tla",
            refinement_root / f"{subject}ImplRefinesSpec.cfg",
            refinement_root / f"{subject}ImplRefinesSpec_NEG.tla",
            refinement_root / f"{subject}ImplRefinesSpec_NEG.cfg",
        )
        for path in (record_path, *expected_files):
            if not path.is_file():
                errors.append(f"{subject}: missing correspondence artifact {path.relative_to(primary)}")
                continue
            digest.update(path.relative_to(primary).as_posix().encode("utf-8"))
            digest.update(b"\0")
            digest.update(path.read_bytes())
            digest.update(b"\0")
        if not record_path.is_file():
            continue
        try:
            record = json.loads(record_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            errors.append(f"{subject}: unreadable derivation record: {error}")
            continue
        if not isinstance(record, dict):
            errors.append(f"{subject}: derivation record must be a JSON object")
            continue
        if record.get("structure") != subject or record.get("module") != subject:
            errors.append(
                f"{subject}: record identity must bind both structure and module to {subject!r}"
            )
        state_fields = record.get("implementation_state_fields")
        state_map = record.get("implementation_state_map")
        if not isinstance(state_fields, list) or not state_fields or not all(
            isinstance(value, str) and value for value in state_fields
        ):
            errors.append(f"{subject}: implementation_state_fields must be a nonempty string list")
            state_fields = []
        if len(state_fields) != len(set(state_fields)):
            errors.append(f"{subject}: implementation_state_fields contains duplicates")
        if not isinstance(state_map, dict):
            errors.append(f"{subject}: implementation_state_map must be an object")
            state_map = {}
        if set(state_map) != set(state_fields):
            errors.append(
                f"{subject}: state-map keys must exactly match implementation_state_fields"
            )
        if not all(isinstance(value, str) and value for value in state_map.values()):
            errors.append(f"{subject}: every implementation state mapping must be nonempty")
        if expected_files[0].is_file():
            refinement_text = expected_files[0].read_text(encoding="utf-8")
            for mapped_field in sorted(set(state_map.values())):
                if re.search(rf"\b{re.escape(mapped_field)}\b", refinement_text) is None:
                    errors.append(
                        f"{subject}: mapped state field {mapped_field!r} is absent from "
                        f"{expected_files[0].relative_to(primary)}"
                    )
        state_field_count += len(state_fields)

        canonical_actions = record.get("canonical_actions")
        executable_actions = record.get("executable_actions")
        action_map = record.get("action_map")
        if not isinstance(canonical_actions, list) or not canonical_actions or not all(
            isinstance(value, str) and value for value in canonical_actions
        ):
            errors.append(f"{subject}: canonical_actions must be a nonempty string list")
            canonical_actions = []
        if not isinstance(executable_actions, list) or not executable_actions or not all(
            isinstance(value, str) and value for value in executable_actions
        ):
            errors.append(f"{subject}: executable_actions must be a nonempty string list")
            executable_actions = []
        if not isinstance(action_map, dict):
            errors.append(f"{subject}: action_map must be an object")
            action_map = {}
        if set(action_map) != set(canonical_actions):
            errors.append(f"{subject}: action-map keys must exactly match canonical_actions")
        flattened_actions: list[str] = []
        for action, methods in action_map.items():
            if not isinstance(methods, list) or not methods or not all(
                isinstance(value, str) and value for value in methods
            ):
                errors.append(f"{subject}: action_map[{action!r}] must be a nonempty string list")
                continue
            flattened_actions.extend(methods)
        missing_methods = sorted(set(executable_actions) - set(flattened_actions))
        extra_methods = sorted(set(flattened_actions) - set(executable_actions))
        if missing_methods or extra_methods:
            errors.append(
                f"{subject}: executable/action map mismatch: "
                f"missing={missing_methods!r}, extra={extra_methods!r}"
            )
        canonical_action_count += len(canonical_actions)
        executable_action_count += len(executable_actions)
        expected_action_controls.update((subject, action) for action in executable_actions)

        conformance = record.get("conformance_details")
        if not isinstance(conformance, dict):
            errors.append(f"{subject}: conformance_details must be an object")
            conformance = {}
        if set(conformance) != set(IMPLEMENTATION_CONFORMANCE_FIELDS):
            errors.append(
                f"{subject}: conformance_details must contain exactly the common eight-field contract"
            )
        if not all(isinstance(value, str) and value.strip() for value in conformance.values()):
            errors.append(f"{subject}: every conformance detail must be nonempty prose")

        source_checks = record.get("source_checks")
        if not isinstance(source_checks, list) or not source_checks:
            errors.append(f"{subject}: source_checks must be a nonempty list")
            source_checks = []
        checked_source_paths: set[str] = set()
        for index, check in enumerate(source_checks):
            source_check_count += 1
            if not isinstance(check, dict):
                errors.append(f"{subject}: source_checks[{index}] must be an object")
                continue
            raw_path = check.get("path")
            needles = check.get("contains")
            if not isinstance(raw_path, str) or not raw_path:
                errors.append(f"{subject}: source_checks[{index}] has no path")
                continue
            checked_path = resolve_source_locator(primary, raw_path)
            checked_source_paths.add(raw_path)
            if not checked_path.is_file():
                errors.append(f"{subject}: source check path does not exist: {raw_path}")
                continue
            if not isinstance(needles, list) or not needles or not all(
                isinstance(value, str) and value for value in needles
            ):
                errors.append(f"{subject}: source check {raw_path} has no nonempty needles")
                continue
            source_text = checked_path.read_text(encoding="utf-8")
            digest.update(raw_path.encode("utf-8"))
            digest.update(b"\0")
            digest.update(checked_path.read_bytes())
            digest.update(b"\0")
            for needle in needles:
                if needle not in source_text:
                    errors.append(f"{subject}: source check missing {needle!r} in {raw_path}")

        proof_path = expected_files[1].relative_to(primary).as_posix()
        if proof_path not in checked_source_paths:
            errors.append(f"{subject}: source checks do not bind the refinement proof")
        if not any(
            path.startswith(verus_source_prefix)
            for path in checked_source_paths
        ):
            errors.append(f"{subject}: source checks do not bind a Verus carrier")
        if subject in EXECUTION_REFINEMENT_SUBJECTS:
            canonical_source_bound = any(
                path == f"formal/execution/carriers/{subject}.tla"
                for path in checked_source_paths
            )
        else:
            canonical_source_bound = any(
                path.startswith(f"formal/structures/{subject}/")
                and "/refinement/" not in path
                for path in checked_source_paths
            )
        if not canonical_source_bound:
            errors.append(f"{subject}: source checks do not bind a canonical structure module")

        if expected_files[2].is_file():
            properties = config_directives(expected_files[2], "PROPERTY")
            if not properties:
                errors.append(f"{subject}: positive refinement config has no PROPERTY")
        if expected_files[4].is_file():
            negative_properties = config_directives(expected_files[4], "PROPERTY")
            adjacent_invariants = config_directives(expected_files[4], "INVARIANT")
            if len(negative_properties) != 1 or not adjacent_invariants:
                errors.append(
                    f"{subject}: main negative control needs one PROPERTY and adjacent INVARIANT checks"
                )

    missing_action_controls = sorted(expected_action_controls - observed_action_controls)
    extra_action_controls = sorted(observed_action_controls - expected_action_controls)
    if missing_action_controls or extra_action_controls:
        errors.append(
            "action-control inventory mismatch: "
            f"missing={missing_action_controls!r}, extra={extra_action_controls!r}"
        )

    if errors:
        raise ValueError("implementation-refinement correspondence contract failed:\n  " + "\n  ".join(errors))
    return (
        "IMPLEMENTATION_REFINEMENT_CONTRACT|"
        f"subjects={len(IMPLEMENTATION_REFINEMENT_SUBJECTS)}|"
        f"state-fields={state_field_count}|canonical-actions={canonical_action_count}|"
        f"executable-actions={executable_action_count}|"
        f"action-controls={len(observed_action_controls)}|"
        f"control-links={action_control_link_count}|source-checks={source_check_count}|"
        f"sha256={digest.hexdigest()}"
    )


def discover_implementation_items(primary: Path, purposes: dict[str, str]) -> list[WorkItem]:
    root = find_verus_root(primary)
    validate_verus_mutation_registry(primary, root)
    items = [
        WorkItem(
            "primary:construction:ALKRegistry:static:schema-contract",
            "primary",
            "construction",
            "ALKRegistry",
            "registry",
            "static",
            primary / "formal" / "construction" / "alk" / "ALK_REGISTRY.json",
            None,
            "alk-registry-contract",
            "success",
            "Validates exact schema, carrier, clause, mode, predicate, proof-root, assumption, qualifier, outcome, compatibility, and generated-artifact bindings, including rejection controls.",
            role="validation",
        ),
        WorkItem(
            "primary:construction:DerivationArtifacts:static:generated-contract",
            "primary",
            "construction",
            "DerivationArtifacts",
            "derivation",
            "static",
            primary / "formal" / "construction" / "derivations" / "records" / "Budget.json",
            None,
            "derivation-artifact-contract",
            "success",
            "Checks that every derivation data module is the exact generated image of its checked source record.",
            role="validation",
        ),
        WorkItem(
            "primary:implementation:implementation-refinement-contract:static:correspondence-contract",
            "primary",
            "implementation",
            "implementation-refinement-contract",
            "refinement",
            "static",
            primary / "formal" / "construction" / "derivations" / "records" / "Budget.json",
            None,
            "implementation-refinement-contract",
            "success",
            "Validates the common state, action, conformance, source-binding, proof, and control contract for all 23 implementation-refinement packages.",
            role="validation",
            related_subjects=IMPLEMENTATION_REFINEMENT_SUBJECTS,
        ),
        WorkItem(
            "primary:bridge:GovernedCommit:static:translation-certificate",
            "primary",
            "bridge",
            "GovernedCommit",
            "identity",
            "static",
            primary
            / "formal"
            / "construction"
            / "governed-commit-bridge"
            / "TRANSLATION_CERTIFICATE.json",
            None,
            "governed-commit-translation-certificate",
            "success",
            "Recomputes the exact packaged Rust method blocks and TLA+ action identities bound by the governed-commit bridge.",
            role="validation",
            related_subjects=("GovernedCommit",),
        ),
        WorkItem(
            "primary:implementation:catalog:verus:crate",
            "primary",
            "implementation",
            "catalog",
            "implementation-proof",
            "verus",
            root / "src" / "lib.rs",
            None,
            None,
            "success",
            infer_purpose("catalog", "implementation-proof", purposes),
        )
    ]
    for test in sorted((root / "verification" / "known-answer").glob("*.rs")):
        if "fn main" not in test.read_text(encoding="utf-8"):
            continue
        subject = test.stem.removesuffix("_kat").removesuffix("_vectors")
        items.append(
            WorkItem(
                f"primary:implementation:{subject}:rust:{test.stem}",
                "primary",
                "implementation",
                subject,
                "executable-check",
                "rust",
                test,
                None,
                None,
                "success",
                infer_purpose(subject, "executable-check", purposes),
                related_subjects=KAT_RELATED_SUBJECTS.get(test.stem, ()),
            )
        )
    for mutation in VERUS_MUTATIONS:
        source = root / mutation.source
        expected_survivor = mutation.id in VERUS_EXPECTED_SURVIVORS
        items.append(
            WorkItem(
                f"primary:implementation:{mutation.subject}:verus-control:{mutation.id}",
                "primary",
                "implementation",
                mutation.subject,
                "residual" if expected_survivor else "control",
                "verus-control",
                source,
                None,
                mutation.id,
                "success" if expected_survivor else "rejection",
                mutation.purpose,
                role="residual" if expected_survivor else "control",
                mutation=mutation,
            )
        )
    detector_mutation = next(value for value in VERUS_MUTATIONS if value.id == "budget-allocation-credit")
    items.append(
        WorkItem(
            f"primary:implementation:Budget:verus-control:{MUTATION_DETECTOR_SELF_TEST_ID}",
            "primary",
            "implementation",
            "Budget",
            "control",
            "verus-control",
            root / detector_mutation.source,
            None,
            MUTATION_DETECTOR_SELF_TEST_ID,
            "success",
            "Checks that removing the target contract clause makes the paired source mutant escape rejection.",
            mutation=detector_mutation,
        )
    )
    return items


def is_alk_spec_item(item: WorkItem, primary: Path) -> bool:
    spec_root = primary / "formal" / "construction" / "alk" / "spec"
    paths = [item.source]
    if item.config is not None:
        paths.append(item.config)
    return any(spec_root == path or spec_root in path.parents for path in paths)


def normalize_alk_spec_items(items: Sequence[WorkItem], primary: Path) -> list[WorkItem]:
    normalized: list[WorkItem] = []
    for item in items:
        if not is_alk_spec_item(item, primary):
            normalized.append(item)
            continue
        qualifier = item.config.stem if item.config is not None else item.source.stem
        expected = item.expected
        role = "proof" if item.engine == "tlaps" else "model"
        expected_distinct = ALK_SPEC_MODEL_DISTINCT.get(qualifier)
        expected_obligations = 56 if item.engine == "tlaps" else None
        expected_failure = None
        if qualifier in ALK_SPEC_CONTROL_INVARIANTS:
            expected = "violation"
            role = "control"
            expected_failure = ALK_SPEC_CONTROL_INVARIANTS[qualifier]
        normalized.append(
            dataclasses.replace(
                item,
                id=f"primary:alk:{ALK_SPEC_SUBJECT}:{item.engine}:{qualifier}",
                subject=ALK_SPEC_SUBJECT,
                kind="reference-specification",
                expected=expected,
                purpose="Checks one registered part of the bounded ALK-SPEC-1 evidence boundary.",
                role=role,
                expected_distinct=expected_distinct,
                expected_obligations=expected_obligations,
                expected_failure=expected_failure,
            )
        )
    return normalized


def discover_alk_spec_special_items(primary: Path) -> list[WorkItem]:
    spec_root = primary / "formal" / "construction" / "alk" / "spec"
    tla_root = spec_root / "tla"
    vectors = spec_root / "ALK_CONFORMANCE_VECTORS.json"
    execution = tla_root / "ALKConformanceExecution.tla"
    production = tla_root / "ALKReferenceStateMachine.tla"
    purpose = "Checks one registered part of the bounded ALK-SPEC-1 evidence boundary."
    items = [
        WorkItem(
            "primary:alk:ALK-SPEC-1:static:specification-contract",
            "primary",
            "alk",
            ALK_SPEC_SUBJECT,
            "reference-specification",
            "static",
            vectors,
            None,
            "specification-contract",
            "success",
            purpose,
            role="validation",
        ),
        WorkItem(
            "primary:alk:ALK-SPEC-1:static:checker-mutations",
            "primary",
            "alk",
            ALK_SPEC_SUBJECT,
            "reference-specification",
            "static",
            vectors,
            None,
            "checker-mutations",
            "success",
            purpose,
            role="control",
        ),
        WorkItem(
            "primary:alk:ALK-SPEC-1:sany:production-controls-vectors",
            "primary",
            "alk",
            ALK_SPEC_SUBJECT,
            "reference-specification",
            "sany",
            production,
            None,
            "production-controls-vectors",
            "success",
            purpose,
            role="validation",
        ),
    ]
    for variant, (_, _, initial, distinct) in ALK_SPEC_VECTOR_SUITES.items():
        qualifier = variant.replace("/", "-")
        items.append(
            WorkItem(
                f"primary:alk:{ALK_SPEC_SUBJECT}:tlc-vector:{qualifier}",
                "primary",
                "alk",
                ALK_SPEC_SUBJECT,
                "reference-specification",
                "tlc-vector",
                execution,
                None,
                variant,
                "success",
                purpose,
                role="model",
                expected_distinct=distinct,
                expected_initial=initial,
            )
        )
    return items


def discover_items(
    primary: Path,
    supplementary: Path | None,
) -> list[WorkItem]:
    purposes = load_structure_purposes(primary)
    items = discover_tla_items("primary", primary, purposes)
    items = normalize_alk_spec_items(items, primary)
    # Claim, evidence-interface, and normalization controls declare their target last.
    # A parse failure or a violation of an adjacent invariant earns no credit.
    for index, item in enumerate(items):
        if (item.engine == "tlc" and item.expected == "violation"
                and (item.source.name.startswith("ALKClaim") or item.subject in {
                    "EvidenceAttributionMismatch", "EvidenceObligationOmission",
                    "EvidenceTCBOmission", "FloatingEvidenceObligation",
                    "OwnerCommitAlias", "UnsafeObligationAlias"})
                and item.config is not None):
            properties = config_directives(item.config, "PROPERTY")
            invariants = config_directives(item.config, "INVARIANT")
            if len(properties) == 1:
                failure = "property:" + properties[0]
            elif not properties and invariants:
                failure = invariants[-1]
            else:
                raise ValueError(f"claim control has no unique target: {item.config}")
            items[index] = dataclasses.replace(item, expected_failure=failure, role="control")
    items.append(WorkItem(
        "primary:alk:ALK-CLAIM-1:static:claim-certificate-contract",
        "primary", "alk", "ALK-CLAIM-1", "claim-certificate", "static",
        primary / "formal/construction/alk/check_claim_certificate.py",
        None, "claim-certificate-contract", "success",
        "Checks shared claim source bindings and rejects missing ownership, semantic, gate, and residual bindings.",
        role="validation",
    ))
    items.extend(discover_alk_spec_special_items(primary))
    items.extend(discover_implementation_items(primary, purposes))
    if supplementary is not None:
        items.extend(discover_tla_items("supplementary", supplementary, purposes))
    return sorted(items, key=lambda item: item.id.lower())


def add_filters(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--scope", choices=("primary", "supplementary", "all"), default="primary")
    parser.add_argument("--area", action="append", help="Select an area. Repeat for more than one.")
    parser.add_argument("--kind", action="append", help="Select an artifact kind. Repeat for more than one.")
    parser.add_argument(
        "--engine",
        action="append",
        choices=("tlc", "tlc-vector", "tlaps", "sany", "static", "verus", "verus-control", "rust"),
    )
    parser.add_argument("--subject", action="append", help="Select a subject with shell-style wildcards.")
    parser.add_argument("--id", action="append", dest="item_id", help="Select an exact work-item ID.")
    parser.add_argument("--contains", help="Case-insensitive search across IDs, paths, subjects, and purposes.")
    control = parser.add_mutually_exclusive_group()
    control.add_argument("--controls-only", action="store_true")
    control.add_argument("--exclude-controls", action="store_true")


def select_items(items: Sequence[WorkItem], args: argparse.Namespace) -> list[WorkItem]:
    selected: list[WorkItem] = []
    for item in items:
        if args.scope != "all" and item.scope != args.scope:
            continue
        if args.area and item.area not in args.area:
            continue
        if args.kind and item.kind not in args.kind:
            continue
        if args.engine and item.engine not in args.engine:
            continue
        subject_names = (item.subject, *item.related_subjects)
        if args.subject and not any(
            fnmatch.fnmatchcase(subject.lower(), value.lower())
            for subject in subject_names
            for value in args.subject
        ):
            continue
        if args.item_id and item.id not in args.item_id:
            continue
        is_control = item.role == "control" or item.kind in {"control", "control-baseline"}
        if args.controls_only and not is_control:
            continue
        if args.exclude_controls and is_control:
            continue
        if args.contains:
            haystack = " ".join(
                (
                    item.id,
                    item.subject,
                    *item.related_subjects,
                    item.role,
                    item.source.as_posix(),
                    item.purpose,
                )
            ).lower()
            if args.contains.lower() not in haystack:
                continue
        selected.append(item)
    return selected


def has_explicit_selector(args: argparse.Namespace) -> bool:
    return any(
        (
            args.area,
            args.kind,
            args.engine,
            args.subject,
            args.item_id,
            args.contains,
            args.controls_only,
            args.exclude_controls,
        )
    )


def print_item_table(items: Sequence[WorkItem], repository_root: Path) -> None:
    headers = ("ID", "ROLE", "ENGINE", "EXPECTED", "SOURCE")
    rows = [
        (
            item.id,
            item.role,
            item.engine,
            item.expected,
            relative_display(item.source, repository_root),
        )
        for item in items
    ]
    widths = [len(header) for header in headers]
    for row in rows:
        for index, value in enumerate(row):
            widths[index] = min(72, max(widths[index], len(value)))
    print("  ".join(header.ljust(widths[index]) for index, header in enumerate(headers)))
    print("  ".join("-" * width for width in widths))
    for row in rows:
        cells = []
        for index, value in enumerate(row):
            display = value if len(value) <= widths[index] else value[: widths[index] - 3] + "..."
            cells.append(display.ljust(widths[index]))
        print("  ".join(cells))
    for item in items:
        if item.mutation is None:
            continue
        mutation = item.mutation
        print(f"\n{item.id}")
        print(f"  formal module:      {mutation.formal_module}")
        print(f"  executable carrier:  {mutation.executable_carrier}")
        print(f"  carried obligation: {mutation.carried_obligation}")
        print(f"  method or action:   {mutation.affected_action}")
        print(f"  exact source site:  {mutation.source}: {mutation.needle.strip()}")
        print(f"  expected fault:     {mutation.expected_fault}")


SOURCE_FINGERPRINT_IGNORED_PARTS = frozenset(
    {
        ".git",
        ".tlacache",
        ".venv",
        ".verus-cache",
        "__pycache__",
        "_apalache-out",
        "_canon_logs",
        "node_modules",
        "states",
        "target",
    }
)


def source_fingerprint(root: Path) -> str:
    """Bind every mounted non-runtime file, including untracked source files."""
    digest = hashlib.sha256()
    for path in sorted(candidate for candidate in root.rglob("*") if candidate.is_file()):
        rel = path.relative_to(root)
        if any(part in SOURCE_FINGERPRINT_IGNORED_PARTS for part in rel.parts):
            continue
        digest.update(rel.as_posix().encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def normalized_text_sha256(text: str) -> str:
    return hashlib.sha256(text.replace("\r\n", "\n").encode("utf-8")).hexdigest()


def strip_tla_comments(source_text: str) -> str:
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(source_text):
        pair = source_text[index : index + 2]
        character = source_text[index]
        if block_depth:
            if pair == "(*":
                block_depth += 1
                output.extend((" ", " "))
                index += 2
            elif pair == "*)":
                block_depth -= 1
                output.extend((" ", " "))
                index += 2
            else:
                output.append(character if character in "\r\n" else " ")
                index += 1
            continue
        if in_string:
            output.append(character)
            if character == '"':
                backslashes = 0
                cursor = index - 1
                while cursor >= 0 and source_text[cursor] == "\\":
                    backslashes += 1
                    cursor -= 1
                if backslashes % 2 == 0:
                    in_string = False
            index += 1
            continue
        if pair == "\\*":
            while index < len(source_text) and source_text[index] not in "\r\n":
                output.append(" ")
                index += 1
            continue
        if pair == "(*":
            block_depth = 1
            output.extend((" ", " "))
            index += 2
            continue
        output.append(character)
        if character == '"':
            in_string = True
        index += 1
    if block_depth:
        raise ValueError("unterminated TLA+ block comment in production source")
    return "".join(output)


def production_actions(source_text: str) -> set[str]:
    uncommented = strip_tla_comments(source_text)
    next_match = re.search(
        r"^Next ==(?P<body>.*?)^(?:ReferenceTransitionGate\(|Spec ==)",
        uncommented, re.M | re.S,
    )
    if next_match is None:
        raise ValueError("cannot locate the production Next operator")
    live_actions: set[str] = set()
    required_next_constraints = {
        "/\\ UNCHANGED progressState",
        "/\\ PresentedEpochUpdate",
        "/\\ ProfileBridgeUpdate",
        "/\\ <<phase, phase'>> \\in PathTransitions(lastPath')",
    }
    seen_next_constraints: set[str] = set()
    for raw_line in next_match.group("body").splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if line in required_next_constraints:
            if line in seen_next_constraints:
                raise ValueError(f"duplicate production Next constraint: {line}")
            seen_next_constraints.add(line)
            continue
        if line.startswith("/\\ \\/ "):
            action = line[len("/\\ \\/ ") :]
        elif line.startswith("\\/ "):
            action = line[len("\\/ ") :]
        else:
            raise ValueError(f"unparsed production Next line: {raw_line!r}")
        if re.fullmatch(r"[A-Z][A-Za-z0-9_]*", action) is None:
            raise ValueError(f"non-operator production Next branch: {raw_line!r}")
        if action in live_actions:
            raise ValueError(f"duplicate production Next branch: {action}")
        live_actions.add(action)
    if seen_next_constraints != required_next_constraints:
        missing = sorted(required_next_constraints - seen_next_constraints)
        raise ValueError(f"production Next constraint drift: missing {missing}")
    definitions = set(
        re.findall(r"^([A-Z][A-Za-z0-9_]*)\s*==", uncommented, flags=re.M)
    )
    missing_definitions = sorted(live_actions - definitions)
    if missing_definitions:
        raise ValueError(
            f"production Next branches without live definitions: {missing_definitions}"
        )
    return live_actions


def resolved_vector_actions(item: dict[str, object], variant: str) -> list[str]:
    prefixes = item.get("profile_prefixes", {})
    if not isinstance(prefixes, dict):
        raise ValueError(f"invalid profile prefixes: {item.get('id')}")
    actions = item.get("actions", [])
    if not isinstance(actions, list):
        raise ValueError(f"invalid actions: {item.get('id')}")
    return list(prefixes.get(variant, [])) + list(actions)


def resolved_vector_expected(item: dict[str, object], variant: str) -> dict[str, object]:
    expected = item.get("expected", {})
    overrides = item.get("profile_expected_overrides", {})
    if not isinstance(expected, dict) or not isinstance(overrides, dict):
        raise ValueError(f"invalid expected outcome: {item.get('id')}")
    result = dict(expected)
    override = overrides.get(variant, {})
    if not isinstance(override, dict):
        raise ValueError(f"invalid expected override: {item.get('id')}")
    result.update(override)
    return result


def config_string_value(text: str, name: str) -> str | None:
    match = re.search(rf"\b{re.escape(name)}\s*=\s*\"([^\"]+)\"", text)
    return match.group(1) if match else None


def validate_alk_spec_contract(
    primary: Path,
    *,
    data_override: dict[str, object] | None = None,
    source_override: str | None = None,
    execution_override: str | None = None,
    enforce_hashes: bool = True,
) -> str:
    spec_root = primary / "formal" / "construction" / "alk" / "spec"
    tla_root = spec_root / "tla"
    vector_path = spec_root / "ALK_CONFORMANCE_VECTORS.json"
    source_path = tla_root / "ALKReferenceStateMachine.tla"
    execution_path = tla_root / "ALKConformanceExecution.tla"
    control_path = tla_root / "ALKReferenceStateMachineControls.tla"
    proof_path = tla_root / "ALKReferenceStateMachine_Proof.tla"
    required_paths = (vector_path, source_path, execution_path, control_path, proof_path)
    missing_paths = [str(path) for path in required_paths if not path.is_file()]
    if missing_paths:
        raise ValueError("missing ALK-SPEC files: " + ", ".join(missing_paths))

    expected_tla_names = {
        "ALKReferenceStateMachine.tla",
        "ALKReferenceStateMachineControls.tla",
        "ALKReferenceStateMachine_Proof.tla",
        "ALKConformanceExecution.tla",
        *(name + ".cfg" for name in ALK_SPEC_MODEL_DISTINCT),
        *(name + ".cfg" for name in ALK_SPEC_CONTROL_INVARIANTS),
    }
    observed_tla_names = {path.name for path in tla_root.iterdir() if path.is_file()}
    if observed_tla_names != expected_tla_names:
        missing = sorted(expected_tla_names - observed_tla_names)
        extra = sorted(observed_tla_names - expected_tla_names)
        raise ValueError(f"ALK-SPEC file inventory drift: missing={missing} extra={extra}")

    vector_text = vector_path.read_text(encoding="utf-8")
    source_text = source_override if source_override is not None else source_path.read_text(encoding="utf-8")
    execution_text = (
        execution_override
        if execution_override is not None
        else execution_path.read_text(encoding="utf-8")
    )
    if enforce_hashes:
        vector_hash = normalized_text_sha256(vector_text)
        execution_hash = normalized_text_sha256(execution_text)
        if vector_hash != ALK_SPEC_VECTOR_SHA256:
            raise ValueError(f"reference vector ledger hash drift: {vector_hash}")
        if execution_hash != ALK_SPEC_EXECUTION_SHA256:
            raise ValueError(f"reference vector execution module hash drift: {execution_hash}")

    if data_override is None:
        try:
            data = json.loads(vector_text)
        except json.JSONDecodeError as error:
            raise ValueError(f"invalid vector JSON: {error}") from error
    else:
        data = data_override
    if data.get("schema") != "alk-conformance-vectors/v1":
        raise ValueError("vector schema drift")
    if data.get("reference_spec_version") != ALK_SPEC_SUBJECT:
        raise ValueError("reference specification version drift")
    if data.get("profile_variants") != ALK_SPEC_PROFILES:
        raise ValueError("profile variant inventory drift")
    if data.get("path_inventory") != ALK_SPEC_PATHS:
        raise ValueError("path inventory drift")
    if data.get("claim") != (
        "Bounded abstract reference-spec behavior; not implementation "
        "conformance, deployment certification, or an executable bridge."
    ):
        raise ValueError("vector claim ceiling drift")

    vectors = data.get("vectors")
    if not isinstance(vectors, list) or not all(isinstance(item, dict) for item in vectors):
        raise ValueError("vector ledger must be a list of records")
    vector_records: list[dict[str, object]] = vectors
    ids = [item.get("id") for item in vector_records]
    if any(not isinstance(identifier, str) for identifier in ids) or len(ids) != len(set(ids)):
        raise ValueError("duplicate or invalid vector identifiers")
    by_id = {str(item["id"]): item for item in vector_records}

    for variant in ALK_SPEC_PROFILES:
        unavailable = variant == "delegated/unavailable"
        identifier = (
            ("negative" if unavailable else "positive")
            + ".governed-configuration-"
            + variant.replace("/", "-")
        )
        item = by_id.get(identifier)
        expected_actions = (
            ["GovernedConfigurationUpdate", "RejectUnavailableAssurance"]
            if unavailable
            else ["GovernedConfigurationUpdate", "Admit", "PrepareEffect", "CommitAtomic"]
        )
        expected_class = "negative" if unavailable else "positive"
        if (
            item is None
            or item.get("profiles") != [variant]
            or item.get("classification") != expected_class
            or item.get("actions") != expected_actions
        ):
            raise ValueError(f"governed configuration vector drift: {identifier}")
        expected = item.get("expected")
        required = {
            "configuration_version",
            "owner_revision",
            "guarantee_revision",
            "tcb_revision",
            "epoch",
            "credential_epoch",
            "configured_owner",
            "configured_guarantees",
            "configured_tcb",
            "membership",
            "phase",
            "effect_count",
            "effect_owner",
            "response",
        }
        if unavailable:
            required.add("failure")
        if not isinstance(expected, dict) or not required.issubset(expected):
            raise ValueError(f"governed configuration vector drift: {identifier}")
        if any(expected.get(key) != 2 for key in (
            "configuration_version",
            "owner_revision",
            "guarantee_revision",
            "tcb_revision",
            "epoch",
            "credential_epoch",
        )):
            raise ValueError(f"governed configuration version drift: {identifier}")
        if "claim-configuration-v2" not in expected.get("configured_tcb", []):
            raise ValueError(f"governed configuration TCB drift: {identifier}")
        expected_owner = "none" if unavailable else expected.get("configured_owner")
        if expected.get("effect_owner") != expected_owner:
            raise ValueError(f"governed configuration owner drift: {identifier}")

    referenced_profiles: set[str] = set()
    vector_action_names: set[str] = set()
    executable: list[dict[str, object]] = []
    excluded_paths = {path for path, kind in ALK_SPEC_PATHS.items() if kind == "excluded"}
    observed_excluded: set[str] = set()
    distributed_variant = "bounded-distributed/at-commit"
    for item in vector_records:
        identifier = str(item["id"])
        profiles = item.get("profiles")
        actions = item.get("actions")
        expected = item.get("expected")
        classification = item.get("classification")
        if not isinstance(profiles, list) or not all(isinstance(value, str) for value in profiles):
            raise ValueError(f"invalid vector profiles: {identifier}")
        if not isinstance(actions, list) or not all(isinstance(value, str) for value in actions):
            raise ValueError(f"invalid vector actions: {identifier}")
        if not isinstance(expected, dict):
            raise ValueError(f"invalid vector outcome: {identifier}")
        referenced_profiles.update(profiles)
        unknown_prefixes = set(item.get("profile_prefixes", {})) - set(profiles)
        unknown_overrides = set(item.get("profile_expected_overrides", {})) - set(profiles)
        if unknown_prefixes or unknown_overrides:
            raise ValueError(f"profile-specific vector drift: {identifier}")
        requires_reconfiguration = (
            distributed_variant in profiles
            and bool(actions)
            and actions[0] != "GovernedConfigurationUpdate"
            and any(action in {"Admit", "Partition"} for action in actions)
        )
        distributed_prefix = item.get("profile_prefixes", {}).get(distributed_variant, [])
        if requires_reconfiguration != (distributed_prefix == ["GovernedConfigurationUpdate"]):
            raise ValueError(f"distributed vector reconfiguration drift: {identifier}")
        if (
            distributed_prefix
            and expected.get("presented_epoch") == 1
            and item.get("profile_expected_overrides", {}).get(distributed_variant)
            != {"presented_epoch": 2}
        ):
            raise ValueError(f"distributed vector epoch outcome drift: {identifier}")
        attempted_path = item.get("attempted_path")
        if attempted_path is not None:
            if attempted_path not in ALK_SPEC_PATHS:
                raise ValueError(f"unknown attempted path: {identifier}")
            observed_excluded.add(str(attempted_path))
            if ALK_SPEC_PATHS[str(attempted_path)] == "excluded" and actions:
                raise ValueError(f"excluded path gained an executable transition: {identifier}")
        if classification not in {"positive", "negative"}:
            raise ValueError(f"invalid vector kind: {identifier}")
        if actions:
            executable.append(item)
            for variant in profiles:
                resolved_actions = resolved_vector_actions(item, variant)
                vector_action_names.update(resolved_actions)
                required_outcomes = {"phase", "effect_count", "response"}
                if classification == "negative":
                    required_outcomes.add("failure")
                missing_outcomes = sorted(
                    required_outcomes - set(resolved_vector_expected(item, variant))
                )
                if missing_outcomes:
                    raise ValueError(
                        f"executable vector {identifier} lacks required outcomes: {missing_outcomes}"
                    )
        elif expected != {
            "transition": "absent",
            "effect_count": 0,
            "response": "not-expressible",
        }:
            raise ValueError(f"actionless vector {identifier} lacks the exact absence outcome")

    if referenced_profiles != set(ALK_SPEC_PROFILES):
        raise ValueError("vectors do not cover exactly the frozen profile variants")
    if observed_excluded != excluded_paths:
        raise ValueError("excluded paths do not have exact negative vectors")
    if len(vector_records) != 29 or len(executable) != 26:
        raise ValueError("vector ledger must contain exactly 29 vectors and 26 traces")
    binding_count = sum(len(item["profiles"]) for item in executable)
    if binding_count != 106:
        raise ValueError("vector ledger must contain exactly 106 executable bindings")
    live_actions = production_actions(source_text)
    missing_actions = sorted(vector_action_names - live_actions)
    uncovered_actions = sorted(live_actions - vector_action_names)
    if missing_actions:
        raise ValueError(f"vectors reference actions outside production Next: {missing_actions}")
    if uncovered_actions:
        raise ValueError(f"production Next actions lack conformance vectors: {uncovered_actions}")

    for config_name, variant in ALK_SPEC_MODEL_VARIANTS.items():
        config_text = (tla_root / f"{config_name}.cfg").read_text(encoding="utf-8")
        binding = ALK_SPEC_PROFILES[variant]
        if config_string_value(config_text, "Profile") != binding["profile"]:
            raise ValueError(f"profile binding drift: {config_name}")
        if config_string_value(config_text, "AssuranceMode") != binding["assurance_mode"]:
            raise ValueError(f"assurance binding drift: {config_name}")
        if not re.search(r"^\s*SPECIFICATION\s+Spec\s*$", config_text, re.M):
            raise ValueError(f"specification root drift: {config_name}")
        if re.findall(r"^\s*INVARIANT\s+(\w+)\s*$", config_text, re.M) != ["SpecInvariant"]:
            raise ValueError(f"invariant root drift: {config_name}")

    for config_name, primary_invariant in ALK_SPEC_CONTROL_INVARIANTS.items():
        config_text = (tla_root / f"{config_name}.cfg").read_text(encoding="utf-8")
        invariants = re.findall(r"^\s*INVARIANT\s+(\w+)\s*$", config_text, re.M)
        if invariants != ["TypeInvariant", "ControlAdjacentBoundary", primary_invariant]:
            raise ValueError(f"control invariant binding drift: {config_name}: {invariants}")
        if not re.search(r"^\s*SPECIFICATION\s+ControlSpec\s*$", config_text, re.M):
            raise ValueError(f"control specification root drift: {config_name}")

    return (
        f"ALK_SPEC_CONTRACT|vectors={len(vector_records)}|traces={len(executable)}|"
        f"bindings={binding_count}|controls={len(ALK_SPEC_CONTROL_INVARIANTS)}"
    )


def run_alk_spec_checker_mutations(primary: Path) -> str:
    spec_root = primary / "formal" / "construction" / "alk" / "spec"
    source_path = spec_root / "tla" / "ALKReferenceStateMachine.tla"
    vector_path = spec_root / "ALK_CONFORMANCE_VECTORS.json"
    source_text = source_path.read_text(encoding="utf-8")
    baseline = json.loads(vector_path.read_text(encoding="utf-8"))
    validate_alk_spec_contract(primary)
    rejected: list[str] = []

    def require_rejection(
        label: str,
        *,
        data: dict[str, object] | None = None,
        source: str | None = None,
    ) -> None:
        try:
            validate_alk_spec_contract(
                primary,
                data_override=data,
                source_override=source,
                enforce_hashes=False,
            )
        except ValueError:
            rejected.append(label)
            return
        raise ValueError(f"ALK-SPEC checker mutation was not rejected: {label}")

    require_rejection(
        "comment-only-next-binding",
        source=source_text.replace(
            "       \\/ DuplicateSameRequest",
            "       \\* \\/ DuplicateSameRequest",
            1,
        ),
    )
    require_rejection(
        "duplicate-next-branch",
        source=source_text.replace(
            "       \\/ DuplicateSameRequest",
            "       \\/ DuplicateSameRequest\n       \\/ DuplicateSameRequest",
            1,
        ),
    )
    require_rejection(
        "unvectored-live-action",
        source=source_text.replace("Next ==", "AuditOnlyAction == FALSE\n\nNext ==", 1).replace(
            "       \\/ Admit", "       \\/ Admit\n       \\/ AuditOnlyAction", 1
        ),
    )
    require_rejection(
        "detached-profile-bridge",
        source=source_text.replace("    /\\ ProfileBridgeUpdate\n", "", 1),
    )

    data = copy.deepcopy(baseline)
    data["vectors"][0]["actions"].append("CommentOnlyAction")
    require_rejection("unknown-vector-action", data=data)

    data = copy.deepcopy(baseline)
    del data["vectors"][0]["expected"]["effect_count"]
    require_rejection("weakened-executable-outcome", data=data)

    data = copy.deepcopy(baseline)
    excluded = next(item for item in data["vectors"] if item.get("attempted_path"))
    excluded["profile_prefixes"] = {
        "bounded-distributed/at-commit": ["GovernedConfigurationUpdate"]
    }
    excluded["actions"] = ["Admit"]
    require_rejection("executable-excluded-path", data=data)

    data = copy.deepcopy(baseline)
    governed = next(item for item in data["vectors"] if ".governed-configuration-" in item["id"])
    del governed["expected"]["configured_owner"]
    require_rejection("weakened-governed-owner-outcome", data=data)

    data = copy.deepcopy(baseline)
    distributed = next(item for item in data["vectors"] if item["id"] == "positive.atomic-commit")
    distributed["profile_prefixes"] = {}
    require_rejection("distributed-trace-without-reconfiguration", data=data)

    data = copy.deepcopy(baseline)
    identity = next(
        item for item in data["vectors"] if item["id"] == "positive.same-request-duplicate"
    )
    identity["profile_expected_overrides"] = {}
    require_rejection("distributed-stale-identity-outcome", data=data)

    data = copy.deepcopy(baseline)
    governed = next(
        item
        for item in data["vectors"]
        if ".governed-configuration-" in item["id"] and item["classification"] == "positive"
    )
    governed["actions"] = ["GovernedConfigurationUpdate"]
    require_rejection("truncated-governed-execution", data=data)

    if len(rejected) != 11:
        raise ValueError(f"expected 11 rejected checker mutations, observed {len(rejected)}")
    return "ALK_SPEC_CHECKER_SELF_TEST|baseline=pass|mutations=11|rejected=11"


def require_container() -> None:
    if os.environ.get(CONTAINER_MARKER) != "1":
        raise SystemExit(
            "proof execution is container-only; build the verifier image and run this command through its entrypoint"
        )
    if os.getpid() == 1:
        raise SystemExit(
            "the verifier container requires an init reaper; run Docker with --init so exited proof-tool children are reaped"
        )
    source_runner = Path(os.environ.get("AUTOMATION_STRUCTURE_ROOT", DEFAULT_PRIMARY_CONTAINER)) / "verification" / "run_proofs.py"
    if source_runner.is_file():
        running_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        source_hash = hashlib.sha256(source_runner.read_bytes()).hexdigest()
        if running_hash != source_hash:
            raise SystemExit(
                "the container entrypoint does not match the mounted verification/run_proofs.py; rebuild the verifier image"
            )


def run_process(command: Sequence[str], cwd: Path, timeout: int) -> tuple[int, str, float]:
    started = time.monotonic()
    try:
        completed = subprocess.run(
            list(command),
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
            check=False,
        )
        return completed.returncode, completed.stdout, time.monotonic() - started
    except subprocess.TimeoutExpired as error:
        output = error.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        return 124, output + f"\nTIMEOUT after {timeout} seconds\n", time.monotonic() - started


def copy_tla_scope(
    scope_root: Path,
    destination: Path,
    exclude_supplementary: bool = False,
    allow_overwrite: bool = False,
) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    seen: dict[str, Path] = {}
    scratch_parts = {".tlacache", "_apalache-out", "states"}
    candidates = sorted(scope_root.rglob("*.tla")) + sorted(scope_root.rglob("*.cfg"))
    paths = [
        path
        for path in candidates
        if path.is_file()
        and not scratch_parts.intersection(path.relative_to(scope_root).parts)
    ]
    if exclude_supplementary:
        paths = [path for path in paths if "supplementary-research" not in path.relative_to(scope_root).parts]
    for path in paths:
        if path.name in seen:
            raise RuntimeError(f"duplicate flattened TLA+ filename: {path.name}: {seen[path.name]} and {path}")
        seen[path.name] = path
        target = destination / path.name
        if target.exists() and not allow_overwrite:
            raise RuntimeError(f"staged TLA+ filename already exists: {target}")
        shutil.copy2(path, target)
    tlaps_library = Path("/opt/tlaps/lib/tlaps")
    if tlaps_library.is_dir():
        for tool_module in sorted(tlaps_library.glob("*.tla")):
            if tool_module.name not in seen and not (destination / tool_module.name).exists():
                shutil.copy2(tool_module, destination / tool_module.name)


def command_self_test() -> int:
    require_container()
    with tempfile.TemporaryDirectory(prefix="runner-self-test-") as tmp:
        root = Path(tmp)
        source = root / "source"
        destination = root / "destination"
        (source / "formal").mkdir(parents=True)
        (source / "formal" / "Good.tla").write_text(
            "---- MODULE Good ----\n====\n", encoding="utf-8"
        )
        (source / "formal" / "Directory.tla").mkdir()
        for scratch_name in (".tlacache", "_apalache-out", "states"):
            scratch = source / "formal" / scratch_name / "Scratch.tla"
            scratch.mkdir(parents=True)
            (scratch / "run.txt").write_text("not a module", encoding="utf-8")

        copy_tla_scope(source, destination)
        tlaps_library = Path("/opt/tlaps/lib/tlaps")
        tlaps_modules = {
            path.name for path in tlaps_library.glob("*.tla") if path.is_file()
        }
        staged = sorted(path.name for path in destination.iterdir())
        expected_staged = sorted({"Good.tla"} | tlaps_modules)
        if staged != expected_staged:
            raise AssertionError(f"unexpected staged TLA+ scope: {staged}")

        overlay = root / "overlay"
        overlay.mkdir()
        (overlay / "Good.tla").write_text(
            "---- MODULE Good ----\n\\* overlay\n====\n", encoding="utf-8"
        )
        (overlay / "Local.tla").write_text(
            "---- MODULE Local ----\n====\n", encoding="utf-8"
        )
        copy_tla_scope(overlay, destination, allow_overwrite=True)
        staged = sorted(path.name for path in destination.iterdir())
        expected_staged = sorted({"Good.tla", "Local.tla"} | tlaps_modules)
        if staged != expected_staged:
            raise AssertionError(f"unexpected overlaid TLA+ scope: {staged}")
        if "overlay" not in (destination / "Good.tla").read_text(encoding="utf-8"):
            raise AssertionError("supplementary overlay did not replace the primary module")

        fingerprint_root = root / "fingerprint"
        fingerprint_root.mkdir()
        (fingerprint_root / "source.txt").write_text("source-a", encoding="utf-8")
        fingerprint_before = source_fingerprint(fingerprint_root)
        runtime_output = fingerprint_root / "target" / "debug" / "artifact.bin"
        runtime_output.parent.mkdir(parents=True)
        runtime_output.write_bytes(b"runtime-a")
        if source_fingerprint(fingerprint_root) != fingerprint_before:
            raise AssertionError("runtime target changed the source fingerprint")
        runtime_output.write_bytes(b"runtime-b")
        if source_fingerprint(fingerprint_root) != fingerprint_before:
            raise AssertionError("runtime target mutation changed the source fingerprint")
        (fingerprint_root / "untracked-source.txt").write_text(
            "source-b", encoding="utf-8"
        )
        fingerprint_with_untracked_source = source_fingerprint(fingerprint_root)
        if fingerprint_with_untracked_source == fingerprint_before:
            raise AssertionError("untracked non-runtime source escaped the fingerprint")

        backend_contract = root / "proof-backend-contract"
        backend_contract.mkdir()
        deterministic_proof = backend_contract / "Deterministic_Proof.tla"
        deterministic_proof.write_text(
            "---- MODULE Deterministic_Proof ----\n"
            "(* An outer comment may contain (* nested BY Isa text. *) *)\n"
            'THEOREM Reflexive == "Isa" = "Isa"\n'
            "  OBVIOUS\n"
            "====\n",
            encoding="utf-8",
        )
        if validate_proof_source_contract(
            backend_contract, [deterministic_proof]
        ) != 1:
            raise AssertionError("proof-backend contract did not count its source")
        explicit_isabelle = backend_contract / "ExplicitIsabelle_Proof.tla"
        explicit_isabelle.write_text(
            "---- MODULE ExplicitIsabelle_Proof ----\n"
            "THEOREM Reflexive == TRUE => TRUE\n"
            "  BY Isa\n"
            "====\n",
            encoding="utf-8",
        )
        try:
            validate_proof_source_contract(backend_contract, [explicit_isabelle])
        except RuntimeError as error:
            if "ExplicitIsabelle_Proof.tla:3" not in str(error):
                raise AssertionError(
                    "proof-backend contract rejected the wrong source site"
                ) from error
        else:
            raise AssertionError("proof-backend contract accepted BY Isa")

        risky_sequence_sources = {
            "HeadToAppend_Proof.tla": "HeadTailProperties, AppendIsConcat",
            "HeadToAppendProperties_Proof.tla": "HeadTailProperties, AppendProperties",
            "EmptyToLength_Proof.tla": "EmptySeq, LenProperties",
            "EmptyToAssoc_Proof.tla": "ConcatEmptySeq,\n     ConcatAssociative",
            "UnlistedPair_Proof.tla": "SeqDef, AppendInjectiveSeq",
        }
        for filename, chain in risky_sequence_sources.items():
            risky_sequence = backend_contract / filename
            risky_sequence.write_text(
                f"---- MODULE {risky_sequence.stem} ----\n"
                "THEOREM Reflexive == TRUE => TRUE\n"
                f"  BY {chain}\n"
                "====\n",
                encoding="utf-8",
            )
            try:
                validate_proof_source_contract(backend_contract, [risky_sequence])
            except RuntimeError as error:
                if "compound" not in str(error) or filename not in str(error):
                    raise AssertionError(
                        "proof-source contract rejected the wrong sequence site"
                    ) from error
            else:
                raise AssertionError(
                    f"proof-source contract accepted a compound sequence leaf: {filename}"
                )

        isabelle = Path("/opt/tlaps/lib/tlaps/Isabelle2011-1/bin/isabelle")
        expected_isabelle_tmp = root / "isabelle-temp-contract"
        prior_isabelle_tmp = os.environ.get("ISABELLE_TMP_PREFIX")
        os.environ["ISABELLE_TMP_PREFIX"] = str(expected_isabelle_tmp)
        try:
            code, output, _ = run_process(
                [str(isabelle), "getenv", "-b", "ISABELLE_TMP_PREFIX"],
                root,
                30,
            )
        finally:
            if prior_isabelle_tmp is None:
                os.environ.pop("ISABELLE_TMP_PREFIX", None)
            else:
                os.environ["ISABELLE_TMP_PREFIX"] = prior_isabelle_tmp
        if code != 0 or output.strip() != str(expected_isabelle_tmp):
            raise AssertionError(
                "pinned Isabelle ignored the runner temp prefix: "
                f"rc={code}, observed={output.strip()!r}, "
                f"expected={str(expected_isabelle_tmp)!r}"
            )

    outcome_cases = {
        Path("AdmissionTable_Cycles_FJ_VIO.cfg"): "violation",
        Path("AdmissionTable_Tree_FJ_PASS.cfg"): "success",
        Path("Model_NEG.cfg"): "violation",
        Path("Model_Property_isolated.cfg"): "success",
        Path("ordinary.cfg"): "success",
    }
    observed = {path: expected_tlc_outcome(path) for path in outcome_cases}
    if observed != outcome_cases:
        raise AssertionError(f"unexpected TLC outcome metadata: {observed}")

    print(
        json.dumps(
            {
                "runner_self_test": "pass",
                "source_modules": 1,
                "overlay_modules": 2,
                "scratch_directories_rejected": 3,
                "runtime_fingerprint_paths_ignored": 1,
                "untracked_source_paths_bound": 1,
                "explicit_isabelle_hints_rejected": 1,
                "compound_sequence_leaves_rejected": len(risky_sequence_sources),
                "isabelle_temp_contract": 1,
                "tlaps_library_modules": len(tlaps_modules),
                "outcome_cases": len(outcome_cases),
            },
            indent=2,
        )
    )
    return 0


def tlc_counts(output: str) -> tuple[int | None, int | None]:
    generated_matches = re.findall(r"([0-9][0-9,]*) states generated", output)
    distinct_matches = re.findall(r"([0-9][0-9,]*) distinct states found", output)
    generated = int(generated_matches[-1].replace(",", "")) if generated_matches else None
    distinct = int(distinct_matches[-1].replace(",", "")) if distinct_matches else None
    return generated, distinct


def tlc_signature(output: str) -> tuple[str, str]:
    generated, distinct = tlc_counts(output)
    generated_text = str(generated) if generated is not None else "NA"
    distinct_text = str(distinct) if distinct is not None else "NA"
    violation_patterns = (
        r"Error: Invariant .* is violated",
        r"Error: The invariant of [A-Za-z][A-Za-z0-9_]* is equal to FALSE",
        r"Error: Action property .* is violated",
        r"Error: Temporal property .* was violated",
        r"The following behavior constitutes a counter-example",
    )
    if any(re.search(pattern, output) for pattern in violation_patterns):
        return "violation", f"VIOLATION|generated={generated_text}|distinct={distinct_text}"
    if "Model checking completed. No error has been found" in output:
        return "success", f"OK|generated={generated_text}|distinct={distinct_text}"
    return "failed", f"FAILED|generated={generated_text}|distinct={distinct_text}"


def execute_tlc(item: WorkItem, work: Path, workers: str, timeout: int) -> RunResult:
    assert item.config is not None and item.module is not None
    metadir = work / "states" / item.id.replace(":", "_")
    if metadir.exists():
        shutil.rmtree(metadir)
    command = [
        "java",
        "-cp",
        "/opt/tlaplus/tla2tools.jar",
        "tlc2.TLC",
        item.module,
        "-config",
        item.config.name,
        "-metadir",
        str(metadir),
        "-workers",
        "1" if item.expected == "violation" else workers,
        "-nowarning",
        "-noGenerateSpecTE",
    ]
    code, output, seconds = run_process(command, work, timeout)
    observed, signature = tlc_signature(output)
    status = "pass" if observed == item.expected else "fail"
    generated, distinct = tlc_counts(output)
    initial_invariant_failures = re.findall(
        r"Error: The invariant of ([A-Za-z][A-Za-z0-9_]*) is equal to FALSE",
        output,
    )
    if (distinct is None or distinct < 1) and observed != "violation":
        status = "fail"
        signature += "|state-floor=fail"
    if item.expected_distinct is not None and distinct != item.expected_distinct:
        status = "fail"
        signature += f"|expected-distinct={item.expected_distinct}"
    if item.expected == "success" and code != 0:
        status = "fail"
        signature += f"|rc={code}"
    if item.expected == "violation" and code not in {12, 13}:
        status = "fail"
        signature += f"|unexpected-violation-rc={code}"
    if item.expected_failure is not None:
        failures = re.findall(r"Error: Invariant ([A-Za-z][A-Za-z0-9_]*) is violated", output)
        failures.extend(initial_invariant_failures)
        if item.expected_failure.startswith("property:"):
            expected_property = item.expected_failure.removeprefix("property:")
            configured_properties = config_directives(work / item.config.name, "PROPERTY")
            property_violations = re.findall(
                r"Error: (?:Action property .* is violated|Temporal property .* was violated|Temporal properties were violated\.)",
                output,
            )
            if (
                code != 13
                or failures
                or configured_properties != [expected_property]
                or len(property_violations) != 1
            ):
                status = "fail"
                signature += (
                    f"|expected-failure={item.expected_failure}"
                    f"|configured-properties={','.join(configured_properties) or 'none'}"
                    f"|invariant-failures={','.join(failures) or 'none'}"
                    f"|property-violations={len(property_violations)}|rc={code}"
                )
            else:
                signature += (
                    f"|failure-property={expected_property}|property-violations=1|rc=13"
                )
        elif code != 12 or failures != [item.expected_failure]:
            status = "fail"
            signature += (
                f"|expected-failure={item.expected_failure}|failures={','.join(failures) or 'none'}|rc={code}"
            )
        else:
            signature += f"|failure={item.expected_failure}|rc=12"
    if code == 124:
        status = "timeout"
    return RunResult(item, status, seconds, signature, command, output)


def execute_alk_vector(item: WorkItem, work: Path, timeout: int) -> RunResult:
    assert item.module is not None
    variant = item.module
    profile, assurance, initial, distinct_expected = ALK_SPEC_VECTOR_SUITES[variant]
    config_name = "ALKVector_" + variant.replace("/", "_").replace("-", "_") + ".cfg"
    config = work / config_name
    config.write_text(
        "CONSTANTS\n"
        f'    Profile = "{profile}"\n'
        f'    AssuranceMode = "{assurance}"\n'
        "    MaxAttempts = 2\n\n"
        "INIT VectorInit\n"
        "NEXT VectorAdvance\n\n"
        "INVARIANT SpecInvariant\n"
        "INVARIANT VectorInvariant\n",
        encoding="utf-8",
        newline="\n",
    )
    metadir = work / "states" / item.id.replace(":", "_")
    if metadir.exists():
        shutil.rmtree(metadir)
    command = [
        "java",
        "-cp",
        "/opt/tlaplus/tla2tools.jar",
        "tlc2.TLC",
        "ALKConformanceExecution",
        "-config",
        config.name,
        "-metadir",
        str(metadir),
        "-workers",
        "1",
        "-nowarning",
        "-noGenerateSpecTE",
    ]
    code, output, seconds = run_process(command, work, timeout)
    observed, signature = tlc_signature(output)
    generated, distinct = tlc_counts(output)
    expected_generated = initial + distinct_expected
    status = "pass"
    if observed != "success" or code != 0:
        status = "fail"
    if distinct != distinct_expected or generated != expected_generated:
        status = "fail"
    signature += (
        f"|compatible-initial={initial}|expected-generated={expected_generated}"
        f"|expected-distinct={distinct_expected}|rc={code}"
    )
    if code == 124:
        status = "timeout"
    return RunResult(item, status, seconds, signature, command, output)


def execute_alk_sany(item: WorkItem, work: Path, timeout: int) -> RunResult:
    modules = (
        "ALKReferenceStateMachine.tla",
        "ALKReferenceStateMachineControls.tla",
        "ALKConformanceExecution.tla",
    )
    outputs: list[str] = []
    commands: list[str] = []
    total_seconds = 0.0
    parsed = 0
    for module in modules:
        command = [
            "java",
            "-cp",
            "/opt/tlaplus/tla2tools.jar",
            "tla2sany.SANY",
            module,
        ]
        code, output, seconds = run_process(command, work, timeout)
        commands.extend(command)
        outputs.append(output)
        total_seconds += seconds
        if code != 0 or re.search(r"(?i)(semantic errors|parse error|lexical error|abort)", output):
            return RunResult(
                item,
                "fail",
                total_seconds,
                f"SANY_FAILED|module={module}|rc={code}",
                commands,
                "\n".join(outputs),
            )
        parsed += 1
    return RunResult(
        item,
        "pass" if parsed == 3 else "fail",
        total_seconds,
        f"SANY|parsed={parsed}|expected=3",
        commands,
        "\n".join(outputs),
    )


def run_generated_contract(
    primary: Path, relative_path: Path, module_name: str
) -> str:
    path = primary / relative_path
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise ValueError(f"cannot load static contract checker: {relative_path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    checker = getattr(module, "check_contract", None)
    if not callable(checker):
        raise ValueError(f"static contract checker has no check_contract: {relative_path}")
    return checker(primary)


def execute_static(item: WorkItem, primary: Path) -> RunResult:
    started = time.monotonic()
    try:
        if item.module == "specification-contract":
            signature = validate_alk_spec_contract(primary)
        elif item.module == "checker-mutations":
            signature = run_alk_spec_checker_mutations(primary)
        elif item.module == "implementation-refinement-contract":
            signature = validate_implementation_refinement_contract(primary)
        elif item.module == "governed-commit-translation-certificate":
            signature = validate_governed_commit_certificate(
                primary, find_verus_root(primary)
            )
        elif item.module == "alk-registry-contract":
            signature = run_generated_contract(
                primary,
                Path("formal/construction/alk/generate_registry.py"),
                "alk_registry_contract",
            )
        elif item.module == "claim-certificate-contract":
            signature = run_generated_contract(
                primary,
                Path("formal/construction/alk/check_claim_certificate.py"),
                "alk_claim_certificate_contract",
            )
        elif item.module == "derivation-artifact-contract":
            signature = run_generated_contract(
                primary,
                Path("formal/construction/derivations/generate_artifacts.py"),
                "derivation_artifact_contract",
            )
        else:
            raise ValueError(f"unknown static check: {item.module}")
        return RunResult(item, "pass", time.monotonic() - started, signature, [], signature)
    except (KeyError, OSError, TypeError, ValueError) as error:
        return RunResult(
            item,
            "fail",
            time.monotonic() - started,
            "STATIC_FAILED",
            [],
            str(error),
        )


def tlaps_signature(output: str, module: str) -> tuple[str, str]:
    if re.search(r"(^|[^A-Za-z_])OMITTED([^A-Za-z_]|$)", output):
        return "failed", "OMITTED"
    proved = re.findall(r"All ([0-9]+) obligations proved", output)
    if proved and "tlapm ending abnormally" not in output.lower():
        return "success", f"PROVED|obligations={proved[-1]}|module={module}"
    return "failed", f"FAILED|module={module}"


def execute_tlaps(item: WorkItem, work: Path, timeout: int) -> RunResult:
    text = (work / item.source.name).read_text(encoding="utf-8")
    if re.search(r"(^|[^A-Za-z_])OMITTED([^A-Za-z_]|$)", text):
        return RunResult(item, "fail", 0.0, "OMITTED", [], "proof source contains OMITTED")
    cache = work / ".tlacache" / f"{item.source.stem}.tlaps"
    if cache.exists():
        shutil.rmtree(cache)
    command = ["tlapm", "--threads", "1", item.source.name]
    code, output, seconds = run_process(command, work, timeout)
    observed, signature = tlaps_signature(output, item.source.stem)
    status = "pass" if observed == "success" else "fail"
    obligations = re.findall(r"All ([0-9]+) obligations proved", output)
    if item.expected_obligations is not None:
        observed_count = int(obligations[-1]) if obligations else None
        if observed_count != item.expected_obligations:
            status = "fail"
            signature += f"|expected-obligations={item.expected_obligations}"
    if code != 0:
        status = "fail"
        signature += f"|rc={code}"
    if code == 124:
        status = "timeout"
    return RunResult(item, status, seconds, signature, command, output)


def execute_verus(item: WorkItem, crate: Path, timeout: int) -> RunResult:
    command = [
        "verus",
        "src/lib.rs",
        "--cfg",
        'feature="proof-api"',
        "--crate-name",
        "automation_structures",
        "--crate-type=lib",
        "--triggers-mode",
        "silent",
        "--multiple-errors",
        "24",
    ]
    code, output, seconds = run_process(command, crate, timeout)
    matches = re.findall(r"verification results::\s*([0-9]+) verified,\s*([0-9]+) errors", output)
    signature = "FAILED"
    status = "fail"
    if matches:
        verified, errors = matches[-1]
        signature = f"VERUS|verified={verified}|errors={errors}"
        status = "pass" if errors == "0" and code == 0 else "fail"
    if code != 0:
        signature += f"|rc={code}"
    if code == 124:
        status = "timeout"
    return RunResult(item, status, seconds, signature, command, output)


def verus_result(output: str) -> tuple[int, int] | None:
    matches = re.findall(r"verification results::\s*([0-9]+) verified,\s*([0-9]+) errors", output)
    if not matches:
        return None
    verified, errors = matches[-1]
    return int(verified), int(errors)


def verify_verus_source(crate: Path, source: str, timeout: int) -> tuple[list[str], int, str, float]:
    command = ["verus", source, "--crate-type=lib", "--triggers-mode", "silent"]
    if source == "src/lib.rs":
        command.extend(
            [
                "--cfg",
                'feature="proof-api"',
                "--crate-name",
                "automation_structures",
                "--multiple-errors",
                "24",
            ]
        )
    code, output, seconds = run_process(command, crate, timeout)
    return command, code, output, seconds


def apply_exact_mutation(path: Path, mutation: Mutation) -> None:
    text = path.read_text(encoding="utf-8")
    if mutation.anchor_start is None:
        if text.count(mutation.needle) != 1:
            raise RuntimeError(
                f"mutation site is not unique for {mutation.id}: {text.count(mutation.needle)} matches"
            )
        updated = text.replace(mutation.needle, mutation.replacement, 1)
    else:
        start = text.find(mutation.anchor_start)
        if start < 0:
            raise RuntimeError(f"mutation start anchor not found for {mutation.id}")
        end = text.find(mutation.anchor_end or "", start)
        if end < 0:
            raise RuntimeError(f"mutation end anchor not found for {mutation.id}")
        segment = text[start:end]
        if segment.count(mutation.needle) != 1:
            raise RuntimeError(
                f"anchored mutation site is not unique for {mutation.id}: {segment.count(mutation.needle)} matches"
            )
        segment = segment.replace(mutation.needle, mutation.replacement, 1)
        updated = text[:start] + segment + text[end:]
    path.write_text(updated, encoding="utf-8")


def execute_verus_control(
    item: WorkItem,
    source_crate: Path,
    mounted_source: Path,
    work_root: Path,
    timeout: int,
) -> RunResult:
    source_before = source_fingerprint(mounted_source)

    def with_custody(result: RunResult) -> RunResult:
        source_after = source_fingerprint(mounted_source)
        if source_after != source_before:
            return dataclasses.replace(
                result,
                status="fail",
                signature=f"{result.signature}|source-custody=changed",
                output=(
                    result.output
                    + f"\nMounted source changed during mutation run: before={source_before} "
                    + f"after={source_after}\n"
                ),
            )
        return dataclasses.replace(result, signature=f"{result.signature}|source-custody=stable")

    if item.module == MUTATION_DETECTOR_SELF_TEST_ID:
        mutation = next(value for value in VERUS_MUTATIONS if value.id == "budget-allocation-credit")
        controls_root = work_root / "verus-controls"
        controls_root.mkdir(parents=True, exist_ok=True)
        crate = Path(tempfile.mkdtemp(prefix=f"{MUTATION_DETECTOR_SELF_TEST_ID}-", dir=controls_root))
        shutil.copytree(source_crate, crate, dirs_exist_ok=True)
        # This is a detector self-test, not a dependency-closure control. Verify
        # the owning module so removing its contract can expose the deliberately
        # undetected body mutation without unrelated consumers retaining errors.
        command, positive_code, positive_output, positive_seconds = verify_verus_source(
            crate, mutation.source, timeout
        )
        positive = verus_result(positive_output)
        if positive_code != 0 or positive is None or positive[1] != 0:
            return with_custody(
                RunResult(
                    item,
                    "timeout" if positive_code == 124 else "fail",
                    positive_seconds,
                    f"POSITIVE_BASELINE_FAILED|rc={positive_code}",
                    command,
                    positive_output,
                )
            )
        contract_clause = Mutation(
            "budget-allocation-contract-removal",
            "Budget",
            mutation.source,
            "            ok ==> final(self).allocated == old(self).allocated + amount,\n",
            "",
            "Detector self-test only.",
        )
        try:
            apply_exact_mutation(crate / mutation.source, contract_clause)
            apply_exact_mutation(crate / mutation.source, mutation)
        except RuntimeError as error:
            return with_custody(
                RunResult(
                    item,
                    "fail",
                    positive_seconds,
                    "MUTATION_SETUP_FAILED",
                    command,
                    positive_output + f"\n{error}\n",
                )
            )
        signatures: list[str] = []
        combined = [positive_output]
        total_seconds = positive_seconds
        for _ in range(2):
            command, mutant_code, mutant_output, mutant_seconds = verify_verus_source(
                crate, mutation.source, timeout
            )
            combined.append(mutant_output)
            total_seconds += mutant_seconds
            result = verus_result(mutant_output)
            if mutant_code != 0 or result is None or result[1] != 0:
                return with_custody(
                    RunResult(
                        item,
                        "timeout" if mutant_code == 124 else "fail",
                        total_seconds,
                        f"DETECTOR_SELF_TEST_REJECTION_REMAINED|rc={mutant_code}",
                        command,
                        "\n".join(combined),
                    )
                )
            signatures.append(
                f"VERUS|verified={result[0]}|errors={result[1]}|rc={mutant_code}"
            )
        stable = signatures[0] == signatures[1]
        return with_custody(
            RunResult(
                item,
                "pass" if stable else "fail",
                total_seconds,
                f"MUTANT_NOT_REJECTED_CONFIRMED|{signatures[0]}|stable={str(stable).lower()}",
                command,
                "\n".join(combined),
            )
        )

    mutation = next(value for value in VERUS_MUTATIONS if value.id == item.module)
    controls_root = work_root / "verus-controls"
    controls_root.mkdir(parents=True, exist_ok=True)
    crate = Path(tempfile.mkdtemp(prefix=f"{mutation.id}-", dir=controls_root))
    shutil.copytree(source_crate, crate, dirs_exist_ok=True)
    verification_root = mutation.verification_root or "src/lib.rs"
    command, positive_code, positive_output, positive_seconds = verify_verus_source(
        crate, verification_root, timeout
    )
    positive = verus_result(positive_output)
    if positive_code != 0 or positive is None or positive[1] != 0:
        return with_custody(
            RunResult(
                item,
                "timeout" if positive_code == 124 else "fail",
                positive_seconds,
                f"POSITIVE_BASELINE_FAILED|rc={positive_code}",
                command,
                positive_output,
            )
        )
    try:
        apply_exact_mutation(crate / mutation.source, mutation)
    except RuntimeError as error:
        return with_custody(
            RunResult(
                item,
                "fail",
                positive_seconds,
                "MUTATION_SETUP_FAILED",
                command,
                positive_output + f"\n{error}\n",
            )
        )
    if mutation.id in VERUS_EXPECTED_SURVIVORS:
        signatures: list[str] = []
        combined = [positive_output]
        total_seconds = positive_seconds
        for _ in range(2):
            command, mutant_code, mutant_output, mutant_seconds = verify_verus_source(
                crate, verification_root, timeout
            )
            combined.append(mutant_output)
            total_seconds += mutant_seconds
            result = verus_result(mutant_output)
            if (
                mutant_code != 0
                or result is None
                or result[1] != 0
                or result[0] != positive[0]
            ):
                observed = (
                    "unreported"
                    if result is None
                    else f"verified={result[0]}|errors={result[1]}"
                )
                return with_custody(
                    RunResult(
                        item,
                        "timeout" if mutant_code == 124 else "fail",
                        total_seconds,
                        f"EXPECTED_SURVIVOR_CHANGED|positive-verified={positive[0]}"
                        f"|mutant={observed}|rc={mutant_code}",
                        command,
                        "\n".join(combined),
                    )
                )
            signatures.append(
                f"VERUS|verified={result[0]}|errors={result[1]}|rc={mutant_code}"
            )
        stable = signatures[0] == signatures[1]
        return with_custody(
            RunResult(
                item,
                "pass" if stable else "fail",
                total_seconds,
                f"KNOWN_RESIDUAL_CONFIRMED|{signatures[0]}|stable={str(stable).lower()}",
                command,
                "\n".join(combined),
            )
        )
    signatures: list[str] = []
    combined = [positive_output]
    total_seconds = positive_seconds
    for _ in range(2):
        mutant_command, mutant_code, mutant_output, mutant_seconds = verify_verus_source(
            crate, verification_root, timeout
        )
        command = mutant_command
        combined.append(mutant_output)
        total_seconds += mutant_seconds
        result = verus_result(mutant_output)
        isolated_rejection = (
            mutant_code == 1
            and result is not None
            and result[1] == 1
            and result[0] + result[1] == positive[0]
        )
        if not isolated_rejection:
            observed = (
                "unreported"
                if result is None
                else f"verified={result[0]}|errors={result[1]}"
            )
            return with_custody(
                RunResult(
                    item,
                    "timeout" if mutant_code == 124 else "fail",
                    total_seconds,
                    f"MUTANT_REJECTION_NOT_ISOLATED|positive-verified={positive[0]}"
                    f"|mutant={observed}|rc={mutant_code}",
                    command,
                    "\n".join(combined),
                )
            )
        signatures.append(
            f"VERUS|verified={result[0]}|errors={result[1]}|rc={mutant_code}"
        )
    stable = signatures[0] == signatures[1]
    return with_custody(
        RunResult(
            item,
            "pass" if stable else "fail",
            total_seconds,
            f"REJECTED|{signatures[0]}|stable={str(stable).lower()}"
            f"|dependency-closure={positive[0] - 1}",
            command,
            "\n".join(combined),
        )
    )


def compile_verus_library(crate: Path, timeout: int) -> tuple[bool, str, float]:
    command = [
        "verus",
        "src/lib.rs",
        "--cfg",
        'feature="proof-api"',
        "--crate-type=lib",
        "--compile",
        "--crate-name",
        "automation_structures",
        "--out-dir",
        ".",
        "--triggers-mode",
        "silent",
        "--multiple-errors",
        "24",
    ]
    code, output, seconds = run_process(command, crate, timeout)
    return code == 0 and (crate / "libautomation_structures.rlib").is_file(), output, seconds


def execute_rust_test(item: WorkItem, crate: Path, timeout: int) -> RunResult:
    verus_dir = Path(os.environ.get("VERUS_BIN", "/opt/verus/verus-x86-linux/verus")).parent
    executable = crate / f"{item.source.stem}.exe"
    command = [
        os.environ.get("RUSTUP_BIN", "rustup"),
        "run",
        "1.95.0",
        "rustc",
        str(crate / "verification" / "known-answer" / item.source.name),
        "--extern",
        f"automation_structures={crate / 'libautomation_structures.rlib'}",
        "--extern",
        f"vstd={verus_dir / 'libvstd.rlib'}",
        "-L",
        f"dependency={verus_dir}",
        "-o",
        str(executable),
    ]
    code, output, build_seconds = run_process(command, crate, timeout)
    if code != 0 or not executable.is_file():
        return RunResult(item, "fail", build_seconds, "RUSTC_FAILED", command, output)
    run_code, run_output, run_seconds = run_process([str(executable)], crate, timeout)
    status = "pass" if run_code == 0 and "KAT_RESULT: FAIL" not in run_output else "fail"
    signature = "KAT_PASS" if status == "pass" else "KAT_FAIL"
    return RunResult(
        item,
        status,
        build_seconds + run_seconds,
        signature,
        command + ["&&", str(executable)],
        output + run_output,
    )


def execute_items(
    selected: Sequence[WorkItem],
    primary: Path,
    supplementary: Path | None,
    args: argparse.Namespace,
) -> list[RunResult]:
    require_container()
    candidates = (RUNTIME_ROOT, Path("/tmp"), Path("/var/tmp"), Path("/usr/tmp"))
    base = next(
        (path for path in candidates if path.is_dir() and os.access(path, os.W_OK)),
        None,
    )
    if base is None:
        raise RuntimeError(
            "no writable temporary directory; mount "
            "--tmpfs /work:rw,exec,nosuid,nodev,size=2g,mode=1777"
        )
    context = tempfile.TemporaryDirectory(prefix="automation-structures-proofs-", dir=base)
    work_root = Path(context.name)
    tool_tmp = work_root / "tool-tmp"
    tool_tmp.mkdir()
    temporary_environment = {
        "TMPDIR": str(tool_tmp),
        "TMP": str(tool_tmp),
        "TEMP": str(tool_tmp),
        "ISABELLE_TMP_PREFIX": str(tool_tmp / "isabelle"),
        "JAVA_TOOL_OPTIONS": f"-Djava.io.tmpdir={tool_tmp}",
    }
    prior_environment = {name: os.environ.get(name) for name in temporary_environment}
    os.environ.update(temporary_environment)
    results: list[RunResult] = []
    try:
        scope_work: dict[tuple[str, str], Path] = {}
        tla_groups = {
            (item.scope, "primary" if item.scope == "primary" else item.area)
            for item in selected
            if item.engine in {"tlc", "tlc-vector", "tlaps", "sany"}
        }
        for scope, group in tla_groups:
            if scope == "primary":
                source_root = primary
            elif supplementary is None:
                source_root = None
            else:
                source_root = supplementary / "studies" / group
            if source_root is None:
                raise RuntimeError(f"source root unavailable for scope {scope}")
            target = work_root / scope / group / "tla"
            if scope == "primary":
                copy_tla_scope(primary, target, exclude_supplementary=True)
            else:
                copy_tla_scope(primary, target, exclude_supplementary=True)
                copy_tla_scope(source_root, target, allow_overwrite=True)
            scope_work[(scope, group)] = target

        verus_items = [item for item in selected if item.engine in {"verus", "verus-control", "rust"}]
        verus_work: Path | None = None
        source_verus: Path | None = None
        if verus_items:
            source_verus = find_verus_root(primary)
            verus_work = work_root / "primary" / "verus"
            shutil.copytree(source_verus, verus_work)

        rust_library_ready = False
        for index, item in enumerate(selected, start=1):
            print(f"[{index}/{len(selected)}] {item.id}", file=sys.stderr)
            tla_group = "primary" if item.scope == "primary" else item.area
            if item.engine == "tlc":
                result = execute_tlc(item, scope_work[(item.scope, tla_group)], args.workers, args.timeout)
            elif item.engine == "tlc-vector":
                result = execute_alk_vector(item, scope_work[(item.scope, tla_group)], args.timeout)
            elif item.engine == "tlaps":
                result = execute_tlaps(item, scope_work[(item.scope, tla_group)], args.timeout)
            elif item.engine == "sany":
                result = execute_alk_sany(item, scope_work[(item.scope, tla_group)], args.timeout)
            elif item.engine == "static":
                result = execute_static(item, primary)
            elif item.engine == "verus":
                assert verus_work is not None
                result = execute_verus(item, verus_work, args.timeout)
            elif item.engine == "verus-control":
                assert source_verus is not None
                result = execute_verus_control(
                    item, source_verus, source_verus, work_root, args.timeout
                )
            elif item.engine == "rust":
                assert verus_work is not None
                if not rust_library_ready:
                    ok, output, seconds = compile_verus_library(verus_work, args.timeout)
                    if not ok:
                        result = RunResult(item, "fail", seconds, "VERUS_COMPILE_FAILED", [], output)
                        results.append(result)
                        if args.fail_fast:
                            break
                        continue
                    rust_library_ready = True
                result = execute_rust_test(item, verus_work, args.timeout)
            else:
                raise RuntimeError(f"unsupported engine: {item.engine}")
            results.append(result)
            print(
                f"  {result.status.upper()} {result.signature} ({result.seconds:.1f}s)",
                file=sys.stderr,
            )
            if result.status != "pass" and args.fail_fast:
                break
    finally:
        for name, value in prior_environment.items():
            if value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = value
        context.cleanup()
    return results


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="run_proofs.py",
        description="Find, explain, and run Automation Structure formal evidence.",
        epilog=(
            "Examples:\n"
            "  run_proofs.py list --area execution\n"
            "  run_proofs.py show Budget\n"
            "  run_proofs.py run --subject Budget --dry-run\n"
            "  run_proofs.py run --area alk --engine tlaps\n"
            "  run_proofs.py run --controls-only --area execution\n"
            "  run_proofs.py run --all --repeat 2 --json results.json"
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    list_parser = subparsers.add_parser("list", help="List available work without running tools.")
    add_filters(list_parser)
    list_parser.add_argument("--json", action="store_true", help="Write JSON to stdout.")

    show_parser = subparsers.add_parser("show", help="Explain a subject or exact work-item ID.")
    show_parser.add_argument("query")
    show_parser.add_argument("--scope", choices=("primary", "supplementary", "all"), default="all")
    show_parser.add_argument("--json", action="store_true")

    run_parser = subparsers.add_parser("run", help="Run an explicit selection inside the container.")
    add_filters(run_parser)
    run_parser.add_argument("--all", action="store_true", help="Run every item allowed by --scope.")
    run_parser.add_argument("--repeat", type=int, choices=range(1, 6), default=1)
    run_parser.add_argument("--workers", default="auto", help="TLC worker count; controls always use one.")
    run_parser.add_argument("--timeout", type=int, default=3600, help="Per-process timeout in seconds.")
    run_parser.add_argument("--fail-fast", action="store_true")
    run_parser.add_argument("--dry-run", action="store_true", help="Print the selection without running tools.")
    run_parser.add_argument(
        "--no-selection-table",
        action="store_true",
        help="Omit per-item rows while retaining selection count and fingerprints.",
    )
    run_parser.add_argument("--json", metavar="PATH", help="Write a machine-readable result file.")
    subparsers.add_parser("doctor", help="Report container and proof-tool identities.")
    subparsers.add_parser("self-test", help="Check runner staging and outcome classification.")
    return parser


def command_list(
    items: Sequence[WorkItem],
    args: argparse.Namespace,
    repository_root: Path,
) -> int:
    selected = select_items(items, args)
    if args.json:
        json.dump([item.record(repository_root) for item in selected], sys.stdout, indent=2)
        print()
    else:
        print_item_table(selected, repository_root)
        print(f"\n{len(selected)} work items")
    return 0


def command_show(
    items: Sequence[WorkItem],
    args: argparse.Namespace,
    repository_root: Path,
) -> int:
    query = args.query.lower()
    matches = [
        item
        for item in items
        if (args.scope == "all" or item.scope == args.scope)
        and (
            item.id.lower() == query
            or item.subject.lower() == query
            or any(subject.lower() == query for subject in item.related_subjects)
        )
    ]
    if not matches:
        matches = [
            item
            for item in items
            if (args.scope == "all" or item.scope == args.scope)
            and query in item.id.lower()
        ]
    if not matches:
        print(f"no formal work matched {args.query!r}", file=sys.stderr)
        return 2
    if args.json:
        json.dump([item.record(repository_root) for item in matches], sys.stdout, indent=2)
        print()
        return 0
    for item in matches:
        record = item.record(repository_root)
        print(item.id)
        print(f"  purpose:  {item.purpose}")
        print(f"  kind:     {item.kind}")
        print(f"  role:     {item.role}")
        print(f"  engine:   {item.engine}")
        print(f"  expected: {item.expected}")
        if item.related_subjects:
            print(f"  aliases:  {', '.join(item.related_subjects)}")
        if item.expected_failure:
            print(f"  seam:     {item.expected_failure}")
        if item.expected_distinct is not None:
            print(f"  states:   {item.expected_distinct} distinct")
        if item.expected_obligations is not None:
            print(f"  proof:    {item.expected_obligations} obligations")
        print(f"  source:   {record['source']}")
        if record["config"]:
            print(f"  config:   {record['config']}")
        if item.mutation is not None:
            mutation = item.mutation
            print(f"  formal:   {mutation.formal_module}")
            print(f"  carrier:  {mutation.executable_carrier}")
            print(f"  binding:  {mutation.carried_obligation}")
            print(f"  action:   {mutation.affected_action}")
            print(f"  site:     {mutation.source}: {mutation.needle.strip()}")
            print(f"  fault:    {mutation.expected_fault}")
        print()
    return 0


def command_doctor(primary: Path) -> int:
    running_runner = Path(__file__)
    source_runner = primary / "verification" / "run_proofs.py"
    running_runner_hash = hashlib.sha256(running_runner.read_bytes()).hexdigest()
    source_runner_hash = (
        hashlib.sha256(source_runner.read_bytes()).hexdigest()
        if source_runner.is_file()
        else None
    )
    tla_jar = Path("/opt/tlaplus/tla2tools.jar")
    tools = {
        "container": os.environ.get(CONTAINER_MARKER, "0"),
        "verifier_version": os.environ.get("AUTOMATION_STRUCTURE_VERIFIER_VERSION", "unreported"),
        "source": str(primary),
        "source_fingerprint": source_fingerprint(primary),
        "installed_runner_sha256": running_runner_hash,
        "source_runner_sha256": source_runner_hash,
        "runner_matches_source": source_runner_hash == running_runner_hash,
        "tla_tools_jar_sha256": (
            hashlib.sha256(tla_jar.read_bytes()).hexdigest() if tla_jar.is_file() else "unavailable"
        ),
    }
    commands = {
        "java": ["java", "-version"],
        "tlc": ["java", "-cp", "/opt/tlaplus/tla2tools.jar", "tlc2.TLC", "-help"],
        "tlaps": ["tlapm", "--version"],
        "verus": ["verus", "--version"],
        "rust": ["rustc", "--version"],
        "python": [sys.executable, "--version"],
    }
    for name, command in commands.items():
        executable = shutil.which(command[0])
        if executable is None:
            tools[name] = "unavailable"
            continue
        code, output, _ = run_process(command, Path.cwd(), 30)
        first = next((line.strip() for line in output.splitlines() if line.strip()), "no output")
        if name == "tlc":
            match = re.search(r"Version ([0-9][0-9.]+)", output)
            first = f"TLC {match.group(1)}" if match else first
        elif name == "verus":
            match = re.search(r"^\s*Version:\s*(.+)$", output, re.M)
            first = f"Verus {match.group(1).strip()}" if match else first
        tools[name] = first if code in {0, 1} else f"error {code}: {first}"
    print(json.dumps(tools, indent=2))
    return 0


def command_run(
    items: Sequence[WorkItem],
    args: argparse.Namespace,
    repository_root: Path,
    primary: Path,
    supplementary: Path | None,
) -> int:
    if not args.all and not has_explicit_selector(args):
        print("run requires a selector or --all; use 'list' to inspect available work", file=sys.stderr)
        return 2
    selected = select_items(items, args)
    if not selected:
        print("the selection contains no work items", file=sys.stderr)
        return 2
    if args.json:
        output_path = Path(args.json).resolve()
        if output_path == primary.resolve() or primary.resolve() in output_path.parents:
            print("result JSON must be written outside the mounted source tree", file=sys.stderr)
            return 2
    if not args.no_selection_table:
        print_item_table(selected, repository_root)
    print(f"\nselected {len(selected)} work items")
    source_before = source_fingerprint(primary)
    selection_fingerprint = hashlib.sha256(
        json.dumps(
            [item.record(repository_root) for item in selected],
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()
    print(f"source fingerprint: {source_before}")
    print(f"selection fingerprint: {selection_fingerprint}")
    if args.dry_run:
        return 0
    repeated = [item for item in selected for _ in range(args.repeat)]
    try:
        results = execute_items(repeated, primary, supplementary, args)
    except (OSError, RuntimeError) as error:
        print(f"proof execution setup failed: {error}", file=sys.stderr)
        return 2
    source_after = source_fingerprint(primary)
    source_stable = source_before == source_after
    observed: dict[str, set[tuple[str, str]]] = {}
    for result in results:
        observed.setdefault(result.item.id, set()).add((result.status, result.signature))
    unstable = {item_id: sorted(values) for item_id, values in observed.items() if len(values) > 1}
    runner_sha256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    payload = {
        "schema": "automation-structure-proof-results-v3",
        "source_fingerprint_before": source_before,
        "source_fingerprint_after": source_after,
        "source_stable": source_stable,
        "selection_fingerprint": selection_fingerprint,
        "runner_sha256": runner_sha256,
        "selection_count": len(selected),
        "execution_count": len(results),
        "repeat": args.repeat,
        "stable": not unstable and source_stable,
        "unstable": unstable,
        "results": [result.record(repository_root) for result in results],
    }
    if args.json:
        output_path = Path(args.json)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    passed = sum(result.status == "pass" for result in results)
    failed = len(results) - passed
    print(f"\nPASS={passed} FAIL={failed}")
    if failed:
        print("failed work items:")
        for result in results:
            if result.status != "pass":
                print(f"  {result.item.id}: {result.status} {result.signature}")
                diagnostic_lines = [line for line in result.output.splitlines() if line.strip()]
                for line in diagnostic_lines[-40:]:
                    print(f"    {line}")
    if unstable:
        print("unstable repeated work items:")
        for item_id, values in unstable.items():
            print(f"  {item_id}: {values}")
    if not source_stable:
        print(f"source changed during execution: before={source_before} after={source_after}")
    return 0 if (
        failed == 0
        and not unstable
        and source_stable
        and len(results) == len(repeated)
    ) else 1


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    require_container()
    repository_root, primary, supplementary = repository_paths()
    if args.command == "doctor":
        return command_doctor(primary)
    if args.command == "self-test":
        return command_self_test()
    try:
        items = discover_items(primary, supplementary)
    except RuntimeError as error:
        print(f"formal-work discovery failed: {error}", file=sys.stderr)
        return 2
    if args.command == "list":
        return command_list(items, args, repository_root)
    if args.command == "show":
        return command_show(items, args, repository_root)
    if args.command == "run":
        return command_run(items, args, repository_root, primary, supplementary)
    parser.error(f"unsupported command: {args.command}")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
