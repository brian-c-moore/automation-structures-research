---- MODULE StepGraphRefinesStreamGraph_Proof ----
(* TLAPS proof of StepGraphRefinesStreamGraph.
   Proves TypeInvariant + UnitOfCompletion (the refinement claim).
   BackpressureDisabled and NoRunBeforePredecessors are TLAPS-proved
   parametrically below.
   BackpressureDisabled is a pointwise consequence of TypeInvariant;
   NoRunBeforePredecessors needs one auxiliary inductive strengthening
   (EligibilityClosed: Ready is granted only under completed
   predecessors, and Completed is absorbing). All four cfg invariants
   are TLAPS-proved for arbitrary RecordsPerEdge \in Nat. *)
EXTENDS StepGraphRefinesStreamGraph, Naturals, Sequences, FiniteSets, TLAPS

ASSUME RecordsPerEdgeType == RecordsPerEdge \in Nat

Inv == TypeInvariant /\ UnitOfCompletion

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    <2>1. nstate \in [Nodes -> NodeStates]
      BY DEF Init, NodeStates, Nodes, Predecessors, Edges
    <2>2. queue \in [Edges -> 0..RecordsPerEdge]
      BY RecordsPerEdgeType DEF Init, Edges
    <2> QED  BY <2>1, <2>2 DEF TypeInvariant
  <1>2. UnitOfCompletion
    \* Init: nstate has no "Completed" nodes; queues are all 0.
    <2> SUFFICES ASSUME NEW e \in Edges
                 PROVE  queue[e] = (IF nstate[e[1]] = "Completed" THEN RecordsPerEdge ELSE 0)
      BY DEF UnitOfCompletion, RefinementMapping
    <2>1. queue[e] = 0                BY DEF Init, Edges
    <2>2. nstate[e[1]] \in {"Ready", "NotReady"}
      BY DEF Init, Edges, Nodes, Predecessors
    <2>3. nstate[e[1]] /= "Completed" BY <2>2
    <2> QED  BY <2>1, <2>3
  <1> QED  BY <1>1, <1>2 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, UnitOfCompletion, RefinementMapping
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE \E n \in Nodes : BecomeReady(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, BecomeReady(n) PROVE Inv'
      BY <1>A
    <2>a. nstate[n] = "NotReady"                        BY DEF BecomeReady
    <2>b. nstate' = [nstate EXCEPT ![n] = "Ready"]      BY DEF BecomeReady
    <2>c. queue' = queue                                BY DEF BecomeReady
    <2>1. nstate' \in [Nodes -> NodeStates]
      BY <2>b DEF TypeInvariant, NodeStates
    <2>2. queue' \in [Edges -> 0..RecordsPerEdge]
      BY <2>c DEF TypeInvariant
    <2>3. UnitOfCompletion'
      <3> SUFFICES ASSUME NEW e \in Edges
                   PROVE queue'[e] = (IF nstate'[e[1]] = "Completed" THEN RecordsPerEdge ELSE 0)
        OBVIOUS
      \* nstate'[e[1]] = nstate[e[1]] unless e[1] = n; in either case
      \* nstate'[e[1]] = "Completed" iff nstate[e[1]] = "Completed".
      \* Because if e[1] = n, then nstate'[n] = "Ready" /= "Completed", and
      \* nstate[n] = "NotReady" /= "Completed".
      <3>1. (nstate'[e[1]] = "Completed") = (nstate[e[1]] = "Completed")
        BY <2>a, <2>b
      <3> QED  BY <2>c, <3>1
    <2> QED  BY <2>1, <2>2, <2>3
  <1>B. CASE \E n \in Nodes : StartRunning(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, StartRunning(n) PROVE Inv'
      BY <1>B
    <2>a. nstate[n] = "Ready"                            BY DEF StartRunning
    <2>b. nstate' = [nstate EXCEPT ![n] = "Running"]     BY DEF StartRunning
    <2>c. queue' = queue                                  BY DEF StartRunning
    <2>1. nstate' \in [Nodes -> NodeStates]
      BY <2>b DEF TypeInvariant, NodeStates
    <2>2. queue' \in [Edges -> 0..RecordsPerEdge]
      BY <2>c DEF TypeInvariant
    <2>3. UnitOfCompletion'
      <3> SUFFICES ASSUME NEW e \in Edges
                   PROVE queue'[e] = (IF nstate'[e[1]] = "Completed" THEN RecordsPerEdge ELSE 0)
        OBVIOUS
      <3>1. (nstate'[e[1]] = "Completed") = (nstate[e[1]] = "Completed")
        BY <2>a, <2>b
      <3> QED  BY <2>c, <3>1
    <2> QED  BY <2>1, <2>2, <2>3
  <1>C. CASE \E n \in Nodes : CompleteAndEmit(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, CompleteAndEmit(n) PROVE Inv'
      BY <1>C
    <2>a. nstate[n] = "Running"                          BY DEF CompleteAndEmit
    <2>b. nstate' = [nstate EXCEPT ![n] = "Completed"]   BY DEF CompleteAndEmit
    <2>c. queue' = [e \in Edges |->
                       IF e[1] = n THEN RecordsPerEdge ELSE queue[e]]
      BY DEF CompleteAndEmit
    <2>1. nstate' \in [Nodes -> NodeStates]
      BY <2>b DEF TypeInvariant, NodeStates
    <2>2. queue' \in [Edges -> 0..RecordsPerEdge]
      BY <2>c, RecordsPerEdgeType DEF TypeInvariant
    <2>3. UnitOfCompletion'
      <3> SUFFICES ASSUME NEW e \in Edges
                   PROVE queue'[e] = (IF nstate'[e[1]] = "Completed" THEN RecordsPerEdge ELSE 0)
        OBVIOUS
      <3>A. CASE e[1] = n
        <4>1. queue'[e] = RecordsPerEdge       BY <2>c, <3>A
        <4>2. nstate'[e[1]] = "Completed"      BY <2>b, <3>A
        <4> QED  BY <4>1, <4>2
      <3>B. CASE e[1] /= n
        <4>1. queue'[e] = queue[e]             BY <2>c, <3>B
        <4>2. nstate'[e[1]] = nstate[e[1]]     BY <2>b, <3>B
        <4>3. queue[e] = (IF nstate[e[1]] = "Completed" THEN RecordsPerEdge ELSE 0)
          OBVIOUS  \* by UnitOfCompletion (inductive hyp)
        <4> QED  BY <4>1, <4>2, <4>3
      <3> QED  BY <3>A, <3>B
    <2> QED  BY <2>1, <2>2, <2>3
  <1>D. CASE Done /\ UNCHANGED vars
    BY <1>D DEF vars
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B, <1>C, <1>D DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv               BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant       BY Safety, PTL DEF Inv
THEOREM UnitOfCompletionSafety == Spec => []UnitOfCompletion  BY Safety, PTL DEF Inv

(* ================================================================== *)
(* The two remaining cfg invariants.                                   *)
(* ================================================================== *)

\* Occupancy never exceeds the batch size: pointwise from typing.
THEOREM BackpressureDisabledSafety == Spec => []BackpressureDisabled
  <1>1. TypeInvariant => BackpressureDisabled
    <2> SUFFICES ASSUME TypeInvariant, NEW e \in Edges
                 PROVE  queue[e] <= RecordsPerEdge
      BY DEF BackpressureDisabled
    <2>1. queue[e] \in 0..RecordsPerEdge
      BY DEF TypeInvariant
    <2> QED  BY <2>1, RecordsPerEdgeType
  <1> QED  BY TypeSafety, <1>1, PTL

\* Auxiliary strengthening: any node at Ready or beyond has all its
\* predecessors Completed. Inductive because BecomeReady grants Ready
\* only under completed predecessors and Completed is absorbing.
EligibilityClosed ==
    \A n \in Nodes :
        nstate[n] \in {"Ready", "Running", "Completed"} =>
            \A q \in Predecessors(n) : nstate[q] = "Completed"

Inv2 == Inv /\ EligibilityClosed

LEMMA InitInv2 == Init => Inv2
  <1> SUFFICES ASSUME Init PROVE Inv2  OBVIOUS
  <1>1. Inv  BY InitInv
  <1>2. EligibilityClosed
    BY DEF Init, EligibilityClosed, Predecessors, Edges, Nodes
  <1> QED  BY <1>1, <1>2 DEF Inv2

LEMMA NextInv2 == Inv2 /\ [Next]_vars => Inv2'
  <1> SUFFICES ASSUME Inv2, [Next]_vars PROVE Inv2'  OBVIOUS
  <1>t. nstate \in [Nodes -> NodeStates]
    BY DEF Inv2, Inv, TypeInvariant
  <1>I. Inv'
    BY NextInv DEF Inv2
  <1>0. CASE UNCHANGED vars
    BY <1>0, <1>I DEF vars, Inv2, EligibilityClosed
  <1>A. CASE \E n \in Nodes : BecomeReady(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, BecomeReady(n) PROVE Inv2'
      BY <1>A
    <2>a. nstate[n] = "NotReady"
      BY DEF BecomeReady
    <2>b. nstate' = [nstate EXCEPT ![n] = "Ready"]
      BY DEF BecomeReady
    <2>c. \A q \in Predecessors(n) : nstate[q] = "Completed"
      BY DEF BecomeReady
    <2>1. EligibilityClosed'
      <3> SUFFICES ASSUME NEW m \in Nodes,
                          nstate'[m] \in {"Ready", "Running", "Completed"},
                          NEW q \in Predecessors(m)
                   PROVE  nstate'[q] = "Completed"
        BY DEF EligibilityClosed
      <3>q. q \in Nodes
        BY DEF Predecessors
      <3>A. CASE m = n
        \* n's predecessors were Completed already and are # n
        <4>1. nstate[q] = "Completed"
          BY <3>A, <2>c
        <4>2. q # n
          BY <2>a, <4>1
        <4> QED  BY <4>1, <4>2, <2>b, <1>t, <3>q
      <3>B. CASE m # n
        <4>1. nstate[m] \in {"Ready", "Running", "Completed"}
          BY <3>B, <2>b, <1>t
        <4>2. nstate[q] = "Completed"
          BY <4>1 DEF Inv2, EligibilityClosed
        <4>3. q # n
          BY <2>a, <4>2
        <4> QED  BY <4>2, <4>3, <2>b, <1>t, <3>q
      <3> QED  BY <3>A, <3>B
    <2> QED  BY <1>I, <2>1 DEF Inv2
  <1>B. CASE \E n \in Nodes : StartRunning(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, StartRunning(n) PROVE Inv2'
      BY <1>B
    <2>a. nstate[n] = "Ready"
      BY DEF StartRunning
    <2>b. nstate' = [nstate EXCEPT ![n] = "Running"]
      BY DEF StartRunning
    <2>1. EligibilityClosed'
      <3> SUFFICES ASSUME NEW m \in Nodes,
                          nstate'[m] \in {"Ready", "Running", "Completed"},
                          NEW q \in Predecessors(m)
                   PROVE  nstate'[q] = "Completed"
        BY DEF EligibilityClosed
      <3>q. q \in Nodes
        BY DEF Predecessors
      <3>1. nstate[m] \in {"Ready", "Running", "Completed"}
        BY <2>a, <2>b, <1>t
      <3>2. nstate[q] = "Completed"
        BY <3>1 DEF Inv2, EligibilityClosed
      <3>3. q # n
        BY <2>a, <3>2
      <3> QED  BY <3>2, <3>3, <2>b, <1>t, <3>q
    <2> QED  BY <1>I, <2>1 DEF Inv2
  <1>C. CASE \E n \in Nodes : CompleteAndEmit(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, CompleteAndEmit(n) PROVE Inv2'
      BY <1>C
    <2>a. nstate[n] = "Running"
      BY DEF CompleteAndEmit
    <2>b. nstate' = [nstate EXCEPT ![n] = "Completed"]
      BY DEF CompleteAndEmit
    <2>1. EligibilityClosed'
      <3> SUFFICES ASSUME NEW m \in Nodes,
                          nstate'[m] \in {"Ready", "Running", "Completed"},
                          NEW q \in Predecessors(m)
                   PROVE  nstate'[q] = "Completed"
        BY DEF EligibilityClosed
      <3>q. q \in Nodes
        BY DEF Predecessors
      <3>A. CASE q = n
        BY <3>A, <2>b, <1>t, <3>q
      <3>B. CASE q # n
        <4>1. nstate[m] \in {"Ready", "Running", "Completed"}
          BY <2>a, <2>b, <1>t
        <4>2. nstate[q] = "Completed"
          BY <4>1 DEF Inv2, EligibilityClosed
        <4> QED  BY <4>2, <3>B, <2>b, <1>t, <3>q
      <3> QED  BY <3>A, <3>B
    <2> QED  BY <1>I, <2>1 DEF Inv2
  <1>D. CASE Done /\ UNCHANGED vars
    BY <1>D, <1>I DEF vars, Inv2, EligibilityClosed
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B, <1>C, <1>D DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety2 == Spec => []Inv2
  <1>1. Init => Inv2                 BY InitInv2
  <1>2. Inv2 /\ [Next]_vars => Inv2'  BY NextInv2
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM NoRunBeforePredecessorsSafety == Spec => []NoRunBeforePredecessors
  <1>1. Inv2 => NoRunBeforePredecessors
    BY DEF Inv2, EligibilityClosed, NoRunBeforePredecessors
  <1> QED  BY Safety2, <1>1, PTL
====
