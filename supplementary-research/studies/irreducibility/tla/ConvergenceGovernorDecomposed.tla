--------------------- MODULE ConvergenceGovernorDecomposed --------------------
(* Decomposition of ConvergenceGovernor: removes COOLING state, leaving a
   3-state machine (ACTIVE/CONVERGED/AWAKENED). Without the intermediate
   cooling buffer, a single low delta triggers premature convergence.
   TLC finds StableConvergence violated.

   What this unit's counterexample does and does not establish.

   The violated invariant `StableConvergence` is not a checked .cfg invariant
   of the canonical ConvergenceGovernor, whose .cfg checks `TypeInvariant`
   alone -- a type/membership-level predicate preserved by any decomposition,
   so not the invariant atomicity protects.  The base ConvergenceGovernor is
   the observational-degeneracy carrier: it carries no convergence-stability
   governance invariant for a decomposition to break.

   No current governor enforces `StableConvergence`.  ConvergenceGovernor-
   PhaseAware's checked obligations (NoCoolingFromCold, NoSkipping,
   ConvergenceRequiresHistory) are a different discipline -- they require a
   supra-threshold peak observation before convergence, the opposite
   direction -- its COOLING->CONVERGED gate is window-average-based as the
   base's is, and it reachably violates StableConvergence at its own .cfg
   bounds.  `ConvergenceGovernorNaive` is the naive-control witness, an
   instrumented copy of the canonical machine, not a decomposition witness of
   anything.

   Irreducibility implication: the base governor's atomicity-dependence
   cannot be demonstrated against its own checked invariants; the entry's
   decomposition witness is its concept carrier's,
   irreducibility/ConvergenceGovernorPhaseAwareDecomposed. This unit's
   counterexample evidences a property of its own 3-state machine below:
   lazily-evaluated sliding-window convergence admits a post-convergence
   stale-window observation, cooling or not.                                *)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Threshold      \* e.g. 2
CONSTANT HistoryLen     \* e.g. 3 — how many entries needed for stable convergence
CONSTANT MaxDelta       \* e.g. 4
CONSTANT NULL

VARIABLE state, history, pc

vars == <<state, history, pc>>

Init ==
    /\ state = "ACTIVE"
    /\ history = <<>>
    /\ pc = "observe"

(* Observe a new delta value *)
ObserveDelta ==
    /\ pc = "observe"
    /\ \E d \in 0..MaxDelta :
        /\ history' = IF Len(history) < HistoryLen
                       THEN Append(history, d)
                       ELSE Append(Tail(history), d)
        /\ pc' = "evaluate"
    /\ UNCHANGED state

(* Decomposed: converge after ANY single entry below threshold,
   instead of requiring ALL entries below threshold (missing COOLING). *)
EvaluateConvergence ==
    /\ pc = "evaluate"
    /\ state = "ACTIVE"
    /\ Len(history) > 0
    /\ history[Len(history)] < Threshold   \* only checks LAST entry
    /\ state' = "CONVERGED"
    /\ pc' = "observe"
    /\ UNCHANGED history

EvaluateStayActive ==
    /\ pc = "evaluate"
    /\ state = "ACTIVE"
    /\ Len(history) > 0
    /\ history[Len(history)] >= Threshold
    /\ pc' = "observe"
    /\ UNCHANGED <<state, history>>

(* Awaken from converged if a high delta arrives *)
Awaken ==
    /\ pc = "evaluate"
    /\ state = "CONVERGED"
    /\ Len(history) > 0
    /\ history[Len(history)] >= Threshold
    /\ state' = "AWAKENED"
    /\ pc' = "observe"
    /\ UNCHANGED history

StayConverged ==
    /\ pc = "evaluate"
    /\ state = "CONVERGED"
    /\ Len(history) > 0
    /\ history[Len(history)] < Threshold
    /\ pc' = "observe"
    /\ UNCHANGED <<state, history>>

ResumeFromAwakened ==
    /\ pc = "evaluate"
    /\ state = "AWAKENED"
    /\ state' = "ACTIVE"
    /\ pc' = "observe"
    /\ UNCHANGED history

Next ==
    \/ ObserveDelta
    \/ EvaluateConvergence
    \/ EvaluateStayActive
    \/ Awaken
    \/ StayConverged
    \/ ResumeFromAwakened

(* If CONVERGED, ALL history entries should be below threshold.
   The decomposed version violates this — only last entry was checked. *)
AllBelowThreshold(h) ==
    \A i \in 1..Len(h) : h[i] < Threshold

StableConvergence ==
    state = "CONVERGED" => AllBelowThreshold(history)

Spec == Init /\ [][Next]_vars
=============================================================================
