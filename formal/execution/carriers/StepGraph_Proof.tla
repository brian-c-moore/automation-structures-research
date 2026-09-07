---- MODULE StepGraph_Proof ----
(* Carrier-level proof. EligibilityClosed is reused from the active
   StepGraphRefinesStreamGraph proof: Ready is granted only after predecessor
   completion, and later states preserve that fact. *)
EXTENDS StepGraph, Integers, FiniteSets, TLAPS

Inv == TypeInvariant /\ EligibilityClosed

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    BY DEF Init, TypeInvariant, NodeStates
  <1>2. EligibilityClosed
    BY DEF Init, EligibilityClosed, Predecessors
  <1> QED  BY <1>1, <1>2 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1>t. nstate \in [Nodes -> NodeStates]
    BY DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars, Inv, EligibilityClosed, TypeInvariant
  <1>A. CASE \E n \in Nodes : BecomeReady(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, BecomeReady(n) PROVE Inv'
      BY <1>A
    <2>a. nstate[n] = "NotReady"  BY DEF BecomeReady
    <2>b. nstate' = [nstate EXCEPT ![n] = "Ready"]  BY DEF BecomeReady
    <2>c. \A p \in Predecessors(n) : nstate[p] = "Completed"
      BY DEF BecomeReady
    <2>1. TypeInvariant'
      BY <2>b, <1>t DEF TypeInvariant, NodeStates
    <2>2. EligibilityClosed'
      <3> SUFFICES ASSUME NEW m \in Nodes,
                          nstate'[m] \in {"Ready", "Running", "Completed"},
                          NEW p \in Predecessors(m)
                   PROVE nstate'[p] = "Completed"
        BY DEF EligibilityClosed
      <3>p. p \in Nodes  BY DEF Predecessors
      <3>M. CASE m = n
        <4>1. nstate[p] = "Completed"  BY <3>M, <2>c
        <4>2. p # n  BY <2>a, <4>1
        <4> QED  BY <4>1, <4>2, <2>b, <1>t, <3>p
      <3>N. CASE m # n
        <4>1. nstate[m] \in {"Ready", "Running", "Completed"}
          BY <3>N, <2>b, <1>t
        <4>2. nstate[p] = "Completed"
          BY <4>1 DEF Inv, EligibilityClosed
        <4>3. p # n  BY <2>a, <4>2
        <4> QED  BY <4>2, <4>3, <2>b, <1>t, <3>p
      <3> QED  BY <3>M, <3>N
    <2> QED  BY <2>1, <2>2 DEF Inv
  <1>B. CASE \E n \in Nodes : StartRunning(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, StartRunning(n) PROVE Inv'
      BY <1>B
    <2>a. nstate[n] = "Ready"  BY DEF StartRunning
    <2>b. nstate' = [nstate EXCEPT ![n] = "Running"]  BY DEF StartRunning
    <2>1. TypeInvariant'
      BY <2>b, <1>t DEF TypeInvariant, NodeStates
    <2>2. EligibilityClosed'
      <3> SUFFICES ASSUME NEW m \in Nodes,
                          nstate'[m] \in {"Ready", "Running", "Completed"},
                          NEW p \in Predecessors(m)
                   PROVE nstate'[p] = "Completed"
        BY DEF EligibilityClosed
      <3>p. p \in Nodes  BY DEF Predecessors
      <3>1. nstate[m] \in {"Ready", "Running", "Completed"}
        BY <2>a, <2>b, <1>t
      <3>2. nstate[p] = "Completed"
        BY <3>1 DEF Inv, EligibilityClosed
      <3>3. p # n  BY <2>a, <3>2
      <3> QED  BY <3>2, <3>3, <2>b, <1>t, <3>p
    <2> QED  BY <2>1, <2>2 DEF Inv
  <1>C. CASE \E n \in Nodes : CompleteNode(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, CompleteNode(n) PROVE Inv'
      BY <1>C
    <2>a. nstate[n] = "Running"  BY DEF CompleteNode
    <2>b. nstate' = [nstate EXCEPT ![n] = "Completed"]  BY DEF CompleteNode
    <2>1. TypeInvariant'
      BY <2>b, <1>t DEF TypeInvariant, NodeStates
    <2>2. EligibilityClosed'
      <3> SUFFICES ASSUME NEW m \in Nodes,
                          nstate'[m] \in {"Ready", "Running", "Completed"},
                          NEW p \in Predecessors(m)
                   PROVE nstate'[p] = "Completed"
        BY DEF EligibilityClosed
      <3>p. p \in Nodes  BY DEF Predecessors
      <3>P. CASE p = n
        BY <3>P, <2>b, <1>t, <3>p
      <3>N. CASE p # n
        <4>1. nstate[m] \in {"Ready", "Running", "Completed"}
          BY <2>a, <2>b, <1>t
        <4>2. nstate[p] = "Completed"
          BY <4>1 DEF Inv, EligibilityClosed
        <4> QED  BY <4>2, <3>N, <2>b, <1>t, <3>p
      <3> QED  BY <3>P, <3>N
    <2> QED  BY <2>1, <2>2 DEF Inv
  <1>D. CASE DoneStuttering
    BY <1>D DEF DoneStuttering, vars, Inv, EligibilityClosed, TypeInvariant
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B, <1>C, <1>D DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                  BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant  BY Safety, PTL DEF Inv
THEOREM EligibilityClosedSafety == Spec => []EligibilityClosed
  BY Safety, PTL DEF Inv
THEOREM ValidStatesSafety == Spec => []ValidStates
  <1>1. TypeInvariant => ValidStates  BY DEF TypeInvariant, ValidStates
  <1> QED  BY TypeSafety, <1>1, PTL

\* Derived projection; it receives no independent obligation credit.
THEOREM NoRunBeforePredecessorsSafety == Spec => []NoRunBeforePredecessors
  <1>1. Inv => NoRunBeforePredecessors
    BY DEF Inv, EligibilityClosed, NoRunBeforePredecessors
  <1> QED  BY Safety, <1>1, PTL

MonotonicAction ==
    \A n \in Nodes : Rank(nstate'[n]) >= Rank(nstate[n])

LEMMA NextMonotonic == [Next]_vars => [MonotonicAction]_vars
  <1> SUFFICES ASSUME [Next]_vars PROVE [MonotonicAction]_vars  OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars, MonotonicAction
  <1>A. CASE \E n \in Nodes : BecomeReady(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, BecomeReady(n)
                 PROVE MonotonicAction
      BY <1>A
    <2> SUFFICES ASSUME NEW m \in Nodes
                 PROVE Rank(nstate'[m]) >= Rank(nstate[m])
      BY DEF MonotonicAction
    <2>M. CASE m = n  BY <2>M DEF BecomeReady, Rank
    <2>N. CASE m # n
      <3>1. nstate'[m] = nstate[m]  BY <2>N DEF BecomeReady
      <3> QED  BY <3>1 DEF Rank
    <2> QED  BY <2>M, <2>N
  <1>B. CASE \E n \in Nodes : StartRunning(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, StartRunning(n)
                 PROVE MonotonicAction
      BY <1>B
    <2> SUFFICES ASSUME NEW m \in Nodes
                 PROVE Rank(nstate'[m]) >= Rank(nstate[m])
      BY DEF MonotonicAction
    <2>M. CASE m = n  BY <2>M DEF StartRunning, Rank
    <2>N. CASE m # n
      <3>1. nstate'[m] = nstate[m]  BY <2>N DEF StartRunning
      <3> QED  BY <3>1 DEF Rank
    <2> QED  BY <2>M, <2>N
  <1>C. CASE \E n \in Nodes : CompleteNode(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, CompleteNode(n)
                 PROVE MonotonicAction
      BY <1>C
    <2> SUFFICES ASSUME NEW m \in Nodes
                 PROVE Rank(nstate'[m]) >= Rank(nstate[m])
      BY DEF MonotonicAction
    <2>M. CASE m = n  BY <2>M DEF CompleteNode, Rank
    <2>N. CASE m # n
      <3>1. nstate'[m] = nstate[m]  BY <2>N DEF CompleteNode
      <3> QED  BY <3>1 DEF Rank
    <2> QED  BY <2>M, <2>N
  <1>D. CASE DoneStuttering
    BY <1>D DEF DoneStuttering, vars, MonotonicAction
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B, <1>C, <1>D DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM ProgressMonotonicSafety == Spec => ProgressMonotonic
  <1>1. Spec => [][Next]_vars  BY DEF Spec
  <1>2. [Next]_vars => [MonotonicAction]_vars  BY NextMonotonic
  <1> QED  BY <1>1, <1>2, PTL DEF ProgressMonotonic, MonotonicAction
====
