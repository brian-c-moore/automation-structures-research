---- MODULE SequentialRefinesStepGraph_Proof ----
(* TLAPS proof of SequentialRefinesStepGraph.
   Proves the two load-bearing invariants: TypeInvariant and
   RefinementMapping. RefinementMapping is the load-bearing refinement
   claim: it says sgstate is always exactly the StepGraph state that
   the Sequential's (pc, active) maps to.
   The two structural invariants (NoRunBeforePredecessors,
   AtMostOneRunning) are TLAPS-proved parametrically below. Both are
   pointwise consequences of Inv: the mapped state ExpectedSGOf(p, a)
   satisfies them for every p \in 0..Steps and a \in BOOLEAN.
   All four cfg invariants are TLAPS-proved for arbitrary Steps. *)
EXTENDS SequentialRefinesStepGraph, Naturals, FiniteSets, FiniteSetTheorems, TLAPS

\* The spec ASSUMEs Steps \in Nat /\ Steps > 0; surfacing it as a named
\* assumption so TLAPS can quote it as needed.
ASSUME StepsType == Steps \in Nat /\ Steps > 0

Inv == TypeInvariant /\ RefinementMapping

LEMMA ExpectedSGOfType ==
    \A p \in 0..Steps, a \in BOOLEAN :
        ExpectedSGOf(p, a) \in [Nodes -> NodeStates]
  <1> SUFFICES ASSUME NEW p \in 0..Steps, NEW a \in BOOLEAN
               PROVE  ExpectedSGOf(p, a) \in [Nodes -> NodeStates]
    OBVIOUS
  <1> QED  BY DEF ExpectedSGOf, NodeStates, Nodes

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    <2>1. pc \in 0..Steps              BY StepsType DEF Init
    <2>2. active \in BOOLEAN           BY DEF Init
    <2>3. sgstate \in [Nodes -> NodeStates]
      BY <2>1, <2>2, ExpectedSGOfType DEF Init
    <2> QED  BY <2>1, <2>2, <2>3 DEF TypeInvariant
  <1>2. RefinementMapping              BY DEF Init, RefinementMapping
  <1> QED  BY <1>1, <1>2 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, RefinementMapping
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE BeginStep
    <2>a. pc \in 0..Steps               BY DEF TypeInvariant
    <2>c. pc < Steps                    BY <1>A DEF BeginStep
    <2>e. pc' = pc + 1                  BY <1>A DEF BeginStep
    <2>f. active' = TRUE                BY <1>A DEF BeginStep
    <2>g. sgstate' = ExpectedSGOf(pc + 1, TRUE)  BY <1>A DEF BeginStep
    <2>1. pc' \in 0..Steps              BY <2>a, <2>c, <2>e, StepsType
    <2>2. active' \in BOOLEAN           BY <2>f
    <2>3. sgstate' \in [Nodes -> NodeStates]
      BY <2>1, <2>e, <2>f, <2>g, ExpectedSGOfType
    <2>4. RefinementMapping'
      BY <2>e, <2>f, <2>g
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>B. CASE CompleteStep
    <2>a. active                        BY <1>B DEF CompleteStep
    <2>b. active' = FALSE               BY <1>B DEF CompleteStep
    <2>c. sgstate' = ExpectedSGOf(pc, FALSE)  BY <1>B DEF CompleteStep
    <2>d. pc' = pc                      BY <1>B DEF CompleteStep, vars
    <2>e. pc \in 0..Steps               BY DEF TypeInvariant
    <2>1. pc' \in 0..Steps              BY <2>d, <2>e
    <2>2. active' \in BOOLEAN           BY <2>b
    <2>3. sgstate' \in [Nodes -> NodeStates]
      BY <2>e, <2>c, ExpectedSGOfType
    <2>4. RefinementMapping'
      BY <2>b, <2>c, <2>d
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>C. CASE DoneStuttering
    BY <1>C DEF DoneStuttering, vars
  <1>D. CASE Next
    BY <1>D, <1>A, <1>B, <1>C DEF Next
  <1> QED  BY <1>0, <1>D

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv               BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant       BY Safety, PTL DEF Inv
THEOREM RefinementSafety == Spec => []RefinementMapping  BY Safety, PTL DEF Inv

(* ================================================================== *)
(* The structural invariants.                                          *)
(* Pointwise lemmas over the mapped state; no transition induction.    *)
(* ================================================================== *)

\* Every mapped state honors StepGraph eligibility: a Running/Completed
\* node's predecessor (its chain neighbor n-1) is Completed.
LEMMA MappedNoRun ==
    \A p \in 0..Steps, a \in BOOLEAN :
        \A n \in Nodes :
            ExpectedSGOf(p, a)[n] \in {"Running", "Completed"} =>
                \A q \in Predecessors(n) : ExpectedSGOf(p, a)[q] = "Completed"
  <1> SUFFICES ASSUME NEW p \in 0..Steps, NEW a \in BOOLEAN,
                      NEW n \in Nodes,
                      ExpectedSGOf(p, a)[n] \in {"Running", "Completed"},
                      NEW q \in Predecessors(n)
               PROVE  ExpectedSGOf(p, a)[q] = "Completed"
    OBVIOUS
  <1>a. n \in 1..Steps /\ q \in 1..Steps /\ n = q + 1
    BY StepsType DEF Predecessors, Edges, Nodes
  <1>b. p \in Nat /\ n \in Nat /\ q \in Nat /\ Steps \in Nat
    BY StepsType, <1>a
  <1>1. \/ n < p \/ (n = p /\ ~a /\ p > 0)
        \/ (n = p /\ a)
    \* the only ExpectedSGOf branches yielding "Running" or "Completed"
    BY <1>a, <1>b DEF ExpectedSGOf, Nodes
  <1>2. q < p
    BY <1>1, <1>a, <1>b
  <1>3. ExpectedSGOf(p, a)[q] = "Completed"
    BY <1>2, <1>a, <1>b DEF ExpectedSGOf, Nodes
  <1> QED  BY <1>3

\* Every mapped state has parallelism degree one: only n = p (when
\* active) maps to "Running", so the Running set is inside {p}.
LEMMA MappedAtMostOne ==
    \A p \in 0..Steps, a \in BOOLEAN :
        Cardinality({n \in Nodes : ExpectedSGOf(p, a)[n] = "Running"}) <= 1
  <1> SUFFICES ASSUME NEW p \in 0..Steps, NEW a \in BOOLEAN
               PROVE  Cardinality({n \in Nodes : ExpectedSGOf(p, a)[n] = "Running"}) <= 1
    OBVIOUS
  <1> DEFINE R == {n \in Nodes : ExpectedSGOf(p, a)[n] = "Running"}
  <1>1. R \subseteq {p}
    BY StepsType DEF ExpectedSGOf, Nodes
  <1>2. IsFiniteSet({p}) /\ Cardinality({p}) = 1
    BY FS_Singleton
  <1>3. IsFiniteSet(R) /\ Cardinality(R) <= Cardinality({p})
    BY <1>1, <1>2, FS_Subset
  <1> QED  BY <1>2, <1>3

THEOREM NoRunBeforePredecessorsSafety == Spec => []NoRunBeforePredecessors
  <1>1. Inv => NoRunBeforePredecessors
    <2> SUFFICES ASSUME Inv PROVE NoRunBeforePredecessors
      OBVIOUS
    <2>1. pc \in 0..Steps /\ active \in BOOLEAN
      BY DEF Inv, TypeInvariant
    <2>2. sgstate = ExpectedSGOf(pc, active)
      BY DEF Inv, RefinementMapping
    <2> QED
      BY <2>1, <2>2, MappedNoRun DEF NoRunBeforePredecessors
  <1> QED  BY Safety, <1>1, PTL

THEOREM AtMostOneRunningSafety == Spec => []AtMostOneRunning
  <1>1. Inv => AtMostOneRunning
    <2> SUFFICES ASSUME Inv PROVE AtMostOneRunning
      OBVIOUS
    <2>1. pc \in 0..Steps /\ active \in BOOLEAN
      BY DEF Inv, TypeInvariant
    <2>2. sgstate = ExpectedSGOf(pc, active)
      BY DEF Inv, RefinementMapping
    <2> QED
      BY <2>1, <2>2, MappedAtMostOne DEF AtMostOneRunning
  <1> QED  BY Safety, <1>1, PTL
====
