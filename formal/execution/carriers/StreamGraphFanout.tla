---- MODULE StreamGraphFanout ----
\* Bounded one-source/two-sink fan-out profile for StreamGraph. SourceIngest
\* broadcasts the same record to both branch queues. Conservation is stated
\* per branch, so one logical input legitimately creates two delivery copies;
\* the superseded scalar equation rejected by StreamGraphFanout_NEG is not
\* reused. Weak fairness of the combined work action is the exact premise for
\* eventual drain; safety and state-level enabledness do not depend on it. The
\* fair source witness below does not restrict Next: SourceIngest still admits
\* every RecordDomain value.

EXTENDS Naturals, Sequences

CONSTANTS Capacity, MaxInputs, RecordDomain

ASSUME CapacityType == Capacity \in Nat /\ Capacity > 0
ASSUME MaxInputsType == MaxInputs \in Nat
ASSUME RecordDomainNonEmpty == RecordDomain # {}

VARIABLES left_queue, right_queue, ingested, left_emitted, right_emitted

vars == <<left_queue, right_queue, ingested, left_emitted, right_emitted>>

TypeInvariant ==
    /\ left_queue \in Seq(RecordDomain)
    /\ right_queue \in Seq(RecordDomain)
    /\ ingested \in 0..MaxInputs
    /\ left_emitted \in 0..MaxInputs
    /\ right_emitted \in 0..MaxInputs

BackpressureCorrect ==
    /\ Len(left_queue) <= Capacity
    /\ Len(right_queue) <= Capacity

\* Each branch accounts for every ingested logical record independently.
PerBranchConservation ==
    /\ ingested = Len(left_queue) + left_emitted
    /\ ingested = Len(right_queue) + right_emitted

\* Derived multiplicity-aware scalar view: every input has two branch copies.
CopyConservation ==
    2 * ingested =
        Len(left_queue) + Len(right_queue) + left_emitted + right_emitted

Init ==
    /\ left_queue = <<>>
    /\ right_queue = <<>>
    /\ ingested = 0
    /\ left_emitted = 0
    /\ right_emitted = 0

SourceIngest ==
    /\ ingested < MaxInputs
    /\ Len(left_queue) < Capacity
    /\ Len(right_queue) < Capacity
    /\ \E v \in RecordDomain :
          /\ left_queue' = Append(left_queue, v)
          /\ right_queue' = Append(right_queue, v)
    /\ ingested' = ingested + 1
    /\ UNCHANGED <<left_emitted, right_emitted>>

ConsumeLeft ==
    /\ Len(left_queue) > 0
    /\ left_queue' = Tail(left_queue)
    /\ left_emitted' = left_emitted + 1
    /\ UNCHANGED <<right_queue, ingested, right_emitted>>

ConsumeRight ==
    /\ Len(right_queue) > 0
    /\ right_queue' = Tail(right_queue)
    /\ right_emitted' = right_emitted + 1
    /\ UNCHANGED <<left_queue, ingested, left_emitted>>

Drain == ConsumeLeft \/ ConsumeRight
Work == SourceIngest \/ Drain

\* A fixed admissible source value gives TLAPS a concrete witness for the
\* fairness action without narrowing SourceIngest's nondeterministic inputs.
FairRecord == CHOOSE v \in RecordDomain : TRUE

FairSourceIngest ==
    /\ ingested < MaxInputs
    /\ Len(left_queue) < Capacity
    /\ Len(right_queue) < Capacity
    /\ left_queue' = Append(left_queue, FairRecord)
    /\ right_queue' = Append(right_queue, FairRecord)
    /\ ingested' = ingested + 1
    /\ UNCHANGED <<left_emitted, right_emitted>>

FairWork == FairSourceIngest \/ Drain

Terminal ==
    /\ ingested = MaxInputs
    /\ Len(left_queue) = 0
    /\ Len(right_queue) = 0

DoneStuttering == Terminal /\ UNCHANGED vars

Next == Work \/ DoneStuttering

Fairness == WF_vars(FairWork)
Spec == Init /\ [][Next]_vars /\ Fairness
UnfairSpec == Init /\ [][Next]_vars

SomeActionEnabled ==
    \/ /\ ingested < MaxInputs
       /\ Len(left_queue) < Capacity
       /\ Len(right_queue) < Capacity
    \/ Len(left_queue) > 0
    \/ Len(right_queue) > 0
    \/ Terminal

\* Compatibility alias only. The formula is state-level action enabledness;
\* EventualDrain below is the separate liveness claim under Fairness.
DeadlockFreedom == SomeActionEnabled
EventualDrain == <>Terminal

\* Natural-valued liveness rank: remaining logical ingress plus the remaining
\* delivery count on each branch. SourceIngest increments ingested; each
\* consume increments its branch counter. Every Work transition decreases the
\* rank by exactly one. PerBranchConservation makes rank zero equivalent to
\* Terminal under Inv.
WorkRemaining ==
    (MaxInputs - ingested) +
    (MaxInputs - left_emitted) +
    (MaxInputs - right_emitted)
====
