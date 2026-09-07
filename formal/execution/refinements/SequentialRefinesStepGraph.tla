---- MODULE SequentialRefinesStepGraph ----
\* Sequential refines StepGraph under a linear topology of N nodes and
\* parallelism degree one. A Sequential program of N steps maps to N
\* linearly-chained nodes 1 -> 2 -> ... -> N, with eligibility
\* constrained so at most one node is Running at a time.
EXTENDS Naturals, FiniteSets

CONSTANTS Steps

ASSUME Steps \in Nat /\ Steps > 0

Nodes == 1..Steps
Edges == {<<i, i+1>> : i \in 1..(Steps - 1)}

NodeStates == {"NotReady", "Ready", "Running", "Completed"}

Predecessors(n) == {p \in Nodes : <<p, n>> \in Edges}

VARIABLES pc, active, sgstate

vars == <<pc, active, sgstate>>

TypeInvariant ==
    /\ pc      \in 0..Steps
    /\ active  \in BOOLEAN
    /\ sgstate \in [Nodes -> NodeStates]

\* Refinement mapping: derive sgstate from (pc, active).
ExpectedSGOf(p, a) ==
    [n \in Nodes |->
        IF n < p \/ (n = p /\ ~a /\ p > 0) THEN "Completed"
        ELSE IF n = p + 1 /\ ~a THEN "Ready"
        ELSE IF n = p /\ a THEN "Running"
        ELSE IF n = 1 /\ p = 0 /\ ~a THEN "Ready"
        ELSE "NotReady"]

Init ==
    /\ pc      = 0
    /\ active  = FALSE
    /\ sgstate = ExpectedSGOf(0, FALSE)

BeginStep ==
    /\ pc < Steps
    /\ ~active
    /\ active' = TRUE
    /\ pc' = pc + 1
    /\ sgstate' = ExpectedSGOf(pc + 1, TRUE)

CompleteStep ==
    /\ active
    /\ active' = FALSE
    /\ sgstate' = ExpectedSGOf(pc, FALSE)
    /\ UNCHANGED pc

DoneStuttering ==
    /\ pc = Steps
    /\ ~active
    /\ UNCHANGED vars

Next == BeginStep \/ CompleteStep \/ DoneStuttering

Spec == Init /\ [][Next]_vars

\* Refinement holds: sgstate matches what the mapping computes.
RefinementMapping == sgstate = ExpectedSGOf(pc, active)

\* StepGraph eligibility: no node Running/Completed unless its
\* predecessor is Completed.
NoRunBeforePredecessors ==
    \A n \in Nodes :
        sgstate[n] \in {"Running", "Completed"} =>
            \A p \in Predecessors(n) : sgstate[p] = "Completed"

\* Parallelism degree one: at most one node Running.
AtMostOneRunning ==
    Cardinality({n \in Nodes : sgstate[n] = "Running"}) <= 1
====
