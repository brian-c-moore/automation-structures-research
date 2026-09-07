---- MODULE TopologyPolicies ----
\* ====================================================================
\* POLICY SPEC: TOPOLOGY (docs/execution-modalities.md)
\*
\* AllPossibleEdges is hardcoded for the sample model because TLC's
\* .cfg parser does not accept tuple-set CONSTANTS.
\* ====================================================================
EXTENDS Naturals, FiniteSets

CONSTANTS Mode, MaxSteps

ASSUME Mode \in {"declared_static", "declared_mutable",
                 "runtime_addressable", "runtime_anonymous"}

Nodes            == {1, 2, 3}
AllPossibleEdges == {<<1, 2>>, <<2, 3>>, <<1, 3>>}

VARIABLES edges, refs, steps

vars == <<edges, refs, steps>>

TypeInvariant ==
    /\ edges \subseteq AllPossibleEdges
    /\ refs  \in [Nodes -> SUBSET Nodes]
    /\ steps \in 0..MaxSteps

Init ==
    /\ refs = [n \in Nodes |-> {}]
    /\ steps = 0
    /\ \/ (Mode = "declared_static"     /\ edges = AllPossibleEdges)
       \/ (Mode = "declared_mutable"    /\ edges = AllPossibleEdges)
       \/ (Mode = "runtime_addressable" /\ edges = {})
       \/ (Mode = "runtime_anonymous"   /\ edges = {})

StaticNoOp ==
    /\ Mode = "declared_static"
    /\ steps < MaxSteps
    /\ steps' = steps + 1
    /\ UNCHANGED <<edges, refs>>

MutableSwap ==
    /\ Mode = "declared_mutable"
    /\ steps < MaxSteps
    /\ \E e \in AllPossibleEdges :
        \/ (e \in edges /\ edges' = edges \ {e})
        \/ (e \notin edges /\ edges' = edges \cup {e})
    /\ steps' = steps + 1
    /\ UNCHANGED refs

LearnRef ==
    /\ Mode = "runtime_addressable"
    /\ steps < MaxSteps
    /\ \E e \in AllPossibleEdges :
        /\ e \notin edges
        /\ refs' = [refs EXCEPT ![e[1]] = refs[e[1]] \cup {e[2]}]
        /\ edges' = edges \cup {e}
    /\ steps' = steps + 1

AnonymousAddEdge ==
    /\ Mode = "runtime_anonymous"
    /\ steps < MaxSteps
    /\ \E e \in AllPossibleEdges :
        /\ e \notin edges
        /\ edges' = edges \cup {e}
    /\ steps' = steps + 1
    /\ UNCHANGED refs

Next ==
    \/ StaticNoOp
    \/ MutableSwap
    \/ LearnRef
    \/ AnonymousAddEdge
    \/ (steps >= MaxSteps /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

EdgesBounded == edges \subseteq AllPossibleEdges

StaticImmutability ==
    Mode = "declared_static" => edges = AllPossibleEdges

AddressableConsistency ==
    Mode = "runtime_addressable" =>
        \A e \in edges : e[2] \in refs[e[1]]

AnonymousNoRefs ==
    Mode = "runtime_anonymous" =>
        \A n \in Nodes : refs[n] = {}
====
