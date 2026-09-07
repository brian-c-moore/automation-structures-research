---- MODULE ForkJoinImplRefinesSpec ----
(***************************************************************************)
(* Executable-contract transcription for the finite ForkJoin carrier.      *)
(* Worker, barrier, output, and terminal calls map to the complete          *)
(* canonical action surface under the identity state observation.          *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, FiniteSets

CONSTANTS Workers, ValueDomain
ASSUME ValueDomainNonEmpty == ValueDomain # {}

VARIABLES wstate, wvalue, phase, output_ready, output_snapshot
vars == <<wstate, wvalue, phase, output_ready, output_snapshot>>

WorkerStates == {"ready", "running", "complete"}
Phases == {"fork", "join", "done"}
AllComplete == \A w \in Workers : wstate[w] = "complete"

TypeInvariant ==
    /\ wstate \in [Workers -> WorkerStates]
    /\ wvalue \in [Workers -> ValueDomain]
    /\ phase \in Phases
    /\ output_ready \in BOOLEAN
    /\ output_snapshot \in [Workers -> ValueDomain]
BarrierCompleteness == output_ready => AllComplete
OutputConsistency == output_ready => output_snapshot = wvalue
PhaseOrdering ==
    /\ (phase = "join" => AllComplete)
    /\ (phase = "done" => output_ready)
ImplInvariant == TypeInvariant /\ BarrierCompleteness /\ OutputConsistency /\ PhaseOrdering

Init ==
    /\ wstate = [w \in Workers |-> "ready"]
    /\ wvalue = [w \in Workers |-> CHOOSE v \in ValueDomain : TRUE]
    /\ phase = "fork"
    /\ output_ready = FALSE
    /\ output_snapshot = [w \in Workers |-> CHOOSE v \in ValueDomain : TRUE]

ImplStartWorker(w) ==
    /\ phase = "fork"
    /\ wstate[w] = "ready"
    /\ wstate' = [wstate EXCEPT ![w] = "running"]
    /\ UNCHANGED <<wvalue, phase, output_ready, output_snapshot>>

ImplCompleteWorker(w, v) ==
    /\ phase = "fork"
    /\ wstate[w] = "running"
    /\ v \in ValueDomain
    /\ wstate' = [wstate EXCEPT ![w] = "complete"]
    /\ wvalue' = [wvalue EXCEPT ![w] = v]
    /\ UNCHANGED <<phase, output_ready, output_snapshot>>

ImplBarrier ==
    /\ phase = "fork"
    /\ AllComplete
    /\ phase' = "join"
    /\ UNCHANGED <<wstate, wvalue, output_ready, output_snapshot>>

ImplProduceOutput ==
    /\ phase = "join"
    /\ output_snapshot' = wvalue
    /\ output_ready' = TRUE
    /\ phase' = "done"
    /\ UNCHANGED <<wstate, wvalue>>

ImplDoneStuttering ==
    /\ phase = "done"
    /\ UNCHANGED vars

ImplNext ==
    \/ \E w \in Workers : ImplStartWorker(w)
    \/ \E w \in Workers, v \in ValueDomain : ImplCompleteWorker(w, v)
    \/ ImplBarrier
    \/ ImplProduceOutput
    \/ ImplDoneStuttering

F == INSTANCE ForkJoin WITH
        Workers <- Workers,
        ValueDomain <- ValueDomain,
        wstate <- wstate,
        wvalue <- wvalue,
        phase <- phase,
        output_ready <- output_ready,
        output_snapshot <- output_snapshot

Spec == Init /\ [][ImplNext]_vars
Refinement == F!Spec
====

