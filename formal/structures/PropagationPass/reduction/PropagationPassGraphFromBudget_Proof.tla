---- MODULE PropagationPassGraphFromBudget_Proof ----
(***************************************************************************
  Parametric refinement proof for the Budget-backed construction.

  Refinement establishes Spec => PPG!Spec, including the target's three weak-
  fairness conjuncts. Five target variables map directly. IterationView maps
  iteration to the Budget allocation ledger minus an in-flight round charge;
  RoundCharged makes this projection a bounded natural.

  For StartRound, each UpdateNode(n), and EndRound, the proof transfers both
  non-stuttering action steps and enabledness, then derives the corresponding
  target weak-fairness conjunct. Assumptions are exactly MaxIterations \in Nat
  and MaxValue \in Nat.
 ***************************************************************************)
EXTENDS PropagationPassGraphFromBudget, FiniteSets, TLAPS

ASSUME MaxIterationsType == MaxIterations \in Nat
ASSUME MaxValueType == MaxValue \in Nat

\* The construction-supplied fact the projection needs: a round in flight has
\* been charged.
RoundCharged == (round = "running") => b_allocated >= 1

Inv == TypeInvariant /\ RoundCharged

(*-------------------------------------------------------------------------*)
(* The construction's combine preserves the declared value range.          *)
(*-------------------------------------------------------------------------*)
LEMMA CombineTyped ==
  ASSUME NEW vals \in [Nodes -> 0..MaxValue], NEW n \in Nodes
  PROVE  Combine(n, vals) \in 0..MaxValue
  <1>A. CASE \E m \in InNbr(n) : vals[m] < vals[n]
    <2>1. PICK m \in InNbr(n) : vals[m] < vals[n]   BY <1>A
    <2>2. m \in Nodes                               BY DEF InNbr
    <2>3. vals[m] \in 0..MaxValue                   BY <2>2
    <2>4. vals[n] \in 0..MaxValue                   OBVIOUS
    <2>5. vals[n] - 1 \in 0..MaxValue
      BY <2>1, <2>3, <2>4, MaxValueType
    <2> QED  BY <1>A, <2>5 DEF Combine
  <1>B. CASE ~(\E m \in InNbr(n) : vals[m] < vals[n])
    <2> QED  BY <1>B DEF Combine
  <1> QED  BY <1>A, <1>B

(*-------------------------------------------------------------------------*)
(* Projection equations for idle and running rounds.                        *)
(*-------------------------------------------------------------------------*)
LEMMA ViewIdle ==
  ASSUME b_allocated \in Nat, round /= "running"
  PROVE  IterationView = b_allocated
  BY DEF IterationView

LEMMA ViewRunning ==
  ASSUME b_allocated \in Nat, round = "running"
  PROVE  IterationView = b_allocated - 1
  BY DEF IterationView

\* Primed projection equations used by action-refinement steps.
LEMMA ViewIdlePrime ==
  ASSUME b_allocated' \in Nat, round' /= "running"
  PROVE  IterationView' = b_allocated'
  BY DEF IterationView

LEMMA ViewRunningPrime ==
  ASSUME b_allocated' \in Nat, round' = "running"
  PROVE  IterationView' = b_allocated' - 1
  BY DEF IterationView

LEMMA ViewStable ==
  ASSUME b_allocated \in Nat, b_allocated' = b_allocated, round' = round
  PROVE  IterationView' = IterationView
  BY DEF IterationView

(*-------------------------------------------------------------------------*)
(* The projection is a natural number, bounded by the capacity.             *)
(*-------------------------------------------------------------------------*)
LEMMA IterViewTyped == Inv => IterationView \in 0..MaxIterations
  <1> SUFFICES ASSUME Inv PROVE IterationView \in 0..MaxIterations  OBVIOUS
  <1>1. b_allocated \in 0..MaxIterations  BY DEF Inv, TypeInvariant
  <1>n. b_allocated \in Nat               BY <1>1, MaxIterationsType
  <1>2. round \in {"idle", "running"}     BY DEF Inv, TypeInvariant
  <1>3. CASE round = "running"
    <2>1. b_allocated >= 1   BY <1>3 DEF Inv, RoundCharged
    <2>2. IterationView = b_allocated - 1  BY <1>n, <1>3, ViewRunning
    <2> QED  BY <2>1, <2>2, <1>1, <1>n, MaxIterationsType
  <1>4. CASE round /= "running"
    <2>1. IterationView = b_allocated  BY <1>n, <1>4, ViewIdle
    <2> QED  BY <2>1, <1>1
  <1> QED  BY <1>3, <1>4

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    BY MaxIterationsType DEF Init, TypeInvariant
  <1>2. RoundCharged
    BY DEF Init, RoundCharged
  <1> QED  BY <1>1, <1>2 DEF Inv

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, RoundCharged
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE CStartRound
    <2> USE <1>A DEF CStartRound
    <2>1. b_allocated' = b_allocated + 1     OBVIOUS
    <2>2. b_allocated + 1 <= b_capacity      OBVIOUS
    <2>3. b_allocated' \in 0..MaxIterations
      BY <2>1, <2>2, MaxIterationsType
    <2> QED  BY <2>1, <2>3, MaxIterationsType
  <1>B. CASE \E n \in Nodes : CUpdateNode(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, CUpdateNode(n) PROVE Inv'
      BY <1>B
    <2> USE DEF CUpdateNode
    <2>1. values' \in [Nodes -> 0..MaxValue]
      <3>1. values \in [Nodes -> 0..MaxValue]   OBVIOUS
      <3>2. snapshot \in [Nodes -> 0..MaxValue] OBVIOUS
      <3>3. Combine(n, snapshot) \in 0..MaxValue  BY <3>2, CombineTyped
      <3> QED  BY <3>1, <3>3
    <2> QED  BY <2>1
  <1>C. CASE CEndRound
    BY <1>C DEF CEndRound
  <1>D. CASE CTerminate
    BY <1>D DEF CTerminate, vars
  <1> QED  BY <1>0, <1>A, <1>B, <1>C, <1>D DEF Next

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                  BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'   BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant  BY Safety, PTL DEF Inv

THEOREM BudgetSafetyPreservation == Spec => []BudgetSafety
  <1>1. Inv => BudgetSafety
    BY MaxIterationsType
       DEF Inv, TypeInvariant, BudgetSafety, Bgt!SafetyInvariant
  <1> QED  BY Safety, <1>1, PTL

(*-------------------------------------------------------------------------*)
(* The safety half of the refinement.                                       *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => PPG!Init
  <1> SUFFICES ASSUME Init PROVE PPG!Init  OBVIOUS
  <1>1. IterationView = 0
    BY DEF Init, IterationView
  <1> QED  BY <1>1 DEF Init, PPG!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [PPG!Next]_(PPG!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [PPG!Next]_(PPG!vars)  OBVIOUS
  <1>c. /\ b_capacity = MaxIterations
        /\ b_allocated \in 0..MaxIterations
        /\ b_reserved = 0
        /\ b_pending = 0
        /\ round \in {"idle", "running"}
        /\ (round = "running") => b_allocated >= 1
    BY DEF Inv, TypeInvariant, RoundCharged
  <1>n. b_allocated \in Nat  BY <1>c, MaxIterationsType

  <1>0. CASE UNCHANGED vars
    <2>1. b_allocated' = b_allocated /\ round' = round  BY <1>0 DEF vars
    <2>2. IterationView' = IterationView    BY <1>n, <2>1, ViewStable
    <2> QED  BY <1>0, <2>2 DEF vars, PPG!vars

  \* ---- round start IS the target's, with the charge landing here ----
  <1>A. CASE CStartRound
    <2> USE <1>A DEF CStartRound
    <2>a. /\ round = "idle"
          /\ changed = TRUE
          /\ b_allocated + b_reserved + b_pending + 1 <= b_capacity
          /\ b_allocated' = b_allocated + 1
          /\ snapshot' = values
          /\ updated' = {}
          /\ round' = "running"
          /\ UNCHANGED <<b_capacity, b_reserved, b_pending, values, changed>>
      OBVIOUS
    <2>n2. b_allocated' \in Nat  BY <2>a, <1>n
    <2>1. IterationView = b_allocated
      BY <1>n, <2>a, ViewIdle
    <2>2. IterationView' = b_allocated' - 1
      BY <2>n2, <2>a, ViewRunningPrime
    <2>3. IterationView' = IterationView
      BY <2>1, <2>2, <2>a, <1>n
    <2>4. IterationView < MaxIterations
      BY <2>a, <2>1, <1>c, <1>n, MaxIterationsType
    <2>5. PPG!StartRound
      BY <2>a, <2>3, <2>4 DEF PPG!StartRound
    <2> QED  BY <2>5 DEF PPG!Next

  \* One node update maps directly after projecting iteration.
  <1>B. CASE \E n \in Nodes : CUpdateNode(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, CUpdateNode(n)
                 PROVE  [PPG!Next]_(PPG!vars)
      BY <1>B
    <2> USE DEF CUpdateNode
    <2>a. /\ round = "running"
          /\ n \notin updated
          /\ values' = [values EXCEPT ![n] = Combine(n, snapshot)]
          /\ updated' = updated \cup {n}
          /\ UNCHANGED <<b_allocated, snapshot, changed, round>>
      OBVIOUS
    <2>1. IterationView' = IterationView
      BY <1>n, <2>a, ViewStable
    <2>2. PPG!Combine(n, snapshot) = Combine(n, snapshot)
      BY DEF PPG!Combine, Combine, PPG!InNbr, InNbr
    <2>3. PPG!UpdateNode(n)
      BY <2>a, <2>1, <2>2 DEF PPG!UpdateNode
    <2> QED  BY <2>3 DEF PPG!Next

  \* ---- round close: the ledger charge becomes the target's increment ----
  <1>C. CASE CEndRound
    <2> USE <1>C DEF CEndRound
    <2>a. /\ round = "running"
          /\ updated = Nodes
          /\ changed' = (values /= snapshot)
          /\ round' = "idle"
          /\ UNCHANGED <<b_allocated, values, snapshot, updated>>
      OBVIOUS
    <2>n2. b_allocated' \in Nat  BY <2>a, <1>n
    <2>1. IterationView = b_allocated - 1
      BY <1>n, <2>a, ViewRunning
    <2>2. IterationView' = b_allocated'
      BY <2>n2, <2>a, ViewIdlePrime
    <2>3. IterationView' = IterationView + 1
      BY <2>1, <2>2, <2>a, <1>c, <1>n
    <2>4. PPG!EndRound
      BY <2>a, <2>3 DEF PPG!EndRound
    <2> QED  BY <2>4 DEF PPG!Next

  \* ---- termination: the ledger reading IS the target's iteration ----
  <1>D. CASE CTerminate
    <2> USE <1>D DEF CTerminate
    <2>a. /\ round = "idle"
          /\ (changed = FALSE \/ b_allocated = MaxIterations)
          /\ UNCHANGED vars
      OBVIOUS
    <2>b. b_allocated' = b_allocated /\ round' = round  BY <2>a DEF vars
    <2>1. IterationView' = IterationView  BY <1>n, <2>b, ViewStable
    <2>2. UNCHANGED PPG!vars
      BY <2>a, <2>1 DEF vars, PPG!vars
    <2> QED  BY <2>2

  <1> QED  BY <1>0, <1>A, <1>B, <1>C, <1>D DEF Next

THEOREM SafetyRefinement == Spec => PPG!Init /\ [][PPG!Next]_(PPG!vars)
  <1>1. Init => PPG!Init                              BY InitRefines
  <1>2. Inv /\ [Next]_vars => [PPG!Next]_(PPG!vars)   BY NextRefines
  <1>3. Spec => []Inv                                 BY Safety
  <1> QED  BY <1>1, <1>2, <1>3, PTL DEF Spec

(*-------------------------------------------------------------------------*)
(* Transfer each weak-fairness conjunct pointwise.                          *)
(*-------------------------------------------------------------------------*)

\* ---- StartRound ------------------------------------------------------------
LEMMA ActionTransferStart ==
  Inv /\ <<CStartRound>>_vars => <<PPG!StartRound>>_(PPG!vars)
  <1> SUFFICES ASSUME Inv, CStartRound
               PROVE  <<PPG!StartRound>>_(PPG!vars)
    OBVIOUS
  <1>c. /\ b_capacity = MaxIterations
        /\ b_allocated \in 0..MaxIterations
    BY DEF Inv, TypeInvariant
  <1>n. b_allocated \in Nat  BY <1>c, MaxIterationsType
  <1>a. /\ round = "idle"
        /\ changed = TRUE
        /\ b_allocated + b_reserved + b_pending + 1 <= b_capacity
        /\ b_allocated' = b_allocated + 1
        /\ snapshot' = values
        /\ updated' = {}
        /\ round' = "running"
        /\ UNCHANGED <<b_capacity, b_reserved, b_pending, values, changed>>
    BY DEF CStartRound
  <1>r. /\ b_reserved = 0
        /\ b_pending = 0
    BY DEF Inv, TypeInvariant
  <1>n2. b_allocated' \in Nat  BY <1>a, <1>n
  <1>1. IterationView = b_allocated        BY <1>n, <1>a, ViewIdle
  <1>2. IterationView' = b_allocated' - 1  BY <1>n2, <1>a, ViewRunningPrime
  <1>3. IterationView' = IterationView     BY <1>1, <1>2, <1>a, <1>n
  <1>4. IterationView < MaxIterations
    BY <1>a, <1>1, <1>c, <1>r, <1>n, MaxIterationsType
  <1>5. PPG!StartRound
    BY <1>a, <1>3, <1>4 DEF PPG!StartRound
  \* Non-stuttering: the round flag is a TARGET variable and it moves.
  <1>6. PPG!vars' # PPG!vars
    BY <1>a DEF PPG!vars
  <1> QED  BY <1>5, <1>6

\* Expand the target and construction actions to transfer enabledness.
LEMMA EnabledTransferStart ==
  ASSUME Inv, ENABLED <<PPG!StartRound>>_(PPG!vars)
  PROVE  ENABLED <<CStartRound>>_vars
  <1> USE DEF PPG!StartRound, PPG!vars, IterationView, CStartRound, vars
  <1>g. round = "idle" /\ changed = TRUE /\ IterationView < MaxIterations
    BY ExpandENABLED, SMT
  <1>c. /\ b_capacity = MaxIterations
        /\ b_allocated \in 0..MaxIterations
        /\ b_reserved = 0
        /\ b_pending = 0
        /\ values \in [Nodes -> 0..MaxValue]
    BY DEF Inv, TypeInvariant
  <1>n. b_allocated \in Nat  BY <1>c, MaxIterationsType
  <1>1. IterationView = b_allocated       BY <1>n, <1>g, ViewIdle
  <1>2. b_allocated + b_reserved + b_pending + 1 <= b_capacity
    BY <1>1, <1>g, <1>c, <1>n, MaxIterationsType
  <1> QED
    BY <1>g, <1>2, <1>c, MaxIterationsType, ExpandENABLED

THEOREM FairnessStart == Spec => WF_(PPG!vars)(PPG!StartRound)
  <1>1. Spec => []Inv                                          BY Safety
  <1>2. Inv /\ <<CStartRound>>_vars => <<PPG!StartRound>>_(PPG!vars)
    BY ActionTransferStart
  <1>3. Inv => (ENABLED <<PPG!StartRound>>_(PPG!vars)
                  => ENABLED <<CStartRound>>_vars)
    BY EnabledTransferStart
  <1> QED  BY <1>1, <1>2, <1>3, PTL DEF Spec, Fairness

\* ---- UpdateNode(n) ---------------------------------------------------------
LEMMA ActionTransferUpdate ==
  ASSUME NEW n \in Nodes, Inv, <<CUpdateNode(n)>>_vars
  PROVE  <<PPG!UpdateNode(n)>>_(PPG!vars)
  <1>c. b_allocated \in 0..MaxIterations  BY DEF Inv, TypeInvariant
  <1>n. b_allocated \in Nat               BY <1>c, MaxIterationsType
  <1>a. /\ round = "running"
        /\ n \notin updated
        /\ values' = [values EXCEPT ![n] = Combine(n, snapshot)]
        /\ updated' = updated \cup {n}
        /\ UNCHANGED <<b_allocated, snapshot, changed, round>>
    BY DEF CUpdateNode
  <1>1. IterationView' = IterationView
    BY <1>n, <1>a, ViewStable
  <1>2. PPG!Combine(n, snapshot) = Combine(n, snapshot)
    BY DEF PPG!Combine, Combine, PPG!InNbr, InNbr
  <1>3. PPG!UpdateNode(n)
    BY <1>a, <1>1, <1>2 DEF PPG!UpdateNode
  \* Non-stuttering: the updated marker set is a TARGET variable and it grows.
  <1>4. PPG!vars' # PPG!vars
    BY <1>a DEF PPG!vars
  <1> QED  BY <1>3, <1>4

LEMMA EnabledTransferUpdate ==
  ASSUME NEW n \in Nodes, Inv, ENABLED <<PPG!UpdateNode(n)>>_(PPG!vars)
  PROVE  ENABLED <<CUpdateNode(n)>>_vars
  <1> USE DEF PPG!UpdateNode, PPG!vars, IterationView, PPG!Combine, PPG!InNbr,
              CUpdateNode, Combine, InNbr, vars
  <1>g. round = "running" /\ n \notin updated
    BY ExpandENABLED, SMT
  <1>c. /\ values \in [Nodes -> 0..MaxValue]
        /\ snapshot \in [Nodes -> 0..MaxValue]
    BY DEF Inv, TypeInvariant
  <1>1. Combine(n, snapshot) \in 0..MaxValue  BY <1>c, CombineTyped
  <1> QED
    BY <1>g, <1>c, <1>1, ExpandENABLED

THEOREM FairnessUpdate ==
  Spec => \A n \in Nodes : WF_(PPG!vars)(PPG!UpdateNode(n))
  <1> SUFFICES ASSUME NEW n \in Nodes
               PROVE  Spec => WF_(PPG!vars)(PPG!UpdateNode(n))
    OBVIOUS
  <1>1. Spec => []Inv                                          BY Safety
  <1>2. Inv /\ <<CUpdateNode(n)>>_vars => <<PPG!UpdateNode(n)>>_(PPG!vars)
    BY ActionTransferUpdate
  <1>3. Inv => (ENABLED <<PPG!UpdateNode(n)>>_(PPG!vars)
                  => ENABLED <<CUpdateNode(n)>>_vars)
    BY EnabledTransferUpdate
  <1>4. Spec => WF_vars(CUpdateNode(n))
    BY DEF Spec, Fairness
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, PTL

\* ---- EndRound --------------------------------------------------------------
LEMMA ActionTransferEnd ==
  Inv /\ <<CEndRound>>_vars => <<PPG!EndRound>>_(PPG!vars)
  <1> SUFFICES ASSUME Inv, CEndRound
               PROVE  <<PPG!EndRound>>_(PPG!vars)
    OBVIOUS
  <1>c. /\ b_allocated \in 0..MaxIterations
        /\ (round = "running") => b_allocated >= 1
    BY DEF Inv, TypeInvariant, RoundCharged
  <1>n. b_allocated \in Nat  BY <1>c, MaxIterationsType
  <1>a. /\ round = "running"
        /\ updated = Nodes
        /\ changed' = (values /= snapshot)
        /\ round' = "idle"
        /\ UNCHANGED <<b_allocated, values, snapshot, updated>>
    BY DEF CEndRound
  <1>n2. b_allocated' \in Nat  BY <1>a, <1>n
  <1>1. IterationView = b_allocated - 1   BY <1>n, <1>a, ViewRunning
  <1>2. IterationView' = b_allocated'     BY <1>n2, <1>a, ViewIdlePrime
  <1>3. IterationView' = IterationView + 1
    BY <1>1, <1>2, <1>c, <1>a, <1>n
  <1>4. PPG!EndRound
    BY <1>a, <1>3 DEF PPG!EndRound
  \* Non-stuttering: the round flag is a TARGET variable and it moves.
  <1>5. PPG!vars' # PPG!vars
    BY <1>a DEF PPG!vars
  <1> QED  BY <1>4, <1>5

LEMMA EnabledTransferEnd ==
  ASSUME Inv, ENABLED <<PPG!EndRound>>_(PPG!vars)
  PROVE  ENABLED <<CEndRound>>_vars
  <1> USE DEF PPG!EndRound, PPG!vars, IterationView, CEndRound, vars
  <1>g. round = "running" /\ updated = Nodes
    BY ExpandENABLED, SMT
  <1>c. /\ values \in [Nodes -> 0..MaxValue]
        /\ snapshot \in [Nodes -> 0..MaxValue]
    BY DEF Inv, TypeInvariant
  <1> QED  BY <1>g, <1>c, ExpandENABLED, SMT

THEOREM FairnessEnd == Spec => WF_(PPG!vars)(PPG!EndRound)
  <1>1. Spec => []Inv                                      BY Safety
  <1>2. Inv /\ <<CEndRound>>_vars => <<PPG!EndRound>>_(PPG!vars)
    BY ActionTransferEnd
  <1>3. Inv => (ENABLED <<PPG!EndRound>>_(PPG!vars)
                  => ENABLED <<CEndRound>>_vars)
    BY EnabledTransferEnd
  <1> QED  BY <1>1, <1>2, <1>3, PTL DEF Spec, Fairness

(*-------------------------------------------------------------------------*)
(* The full refinement: safety + all three fairness conjuncts.              *)
(*-------------------------------------------------------------------------*)
THEOREM Refinement == Spec => PPG!Spec
  <1>1. Spec => PPG!Init /\ [][PPG!Next]_(PPG!vars)  BY SafetyRefinement
  <1>2. Spec => WF_(PPG!vars)(PPG!StartRound)        BY FairnessStart
  <1>3. Spec => \A n \in Nodes : WF_(PPG!vars)(PPG!UpdateNode(n))
    BY FairnessUpdate
  <1>4. Spec => WF_(PPG!vars)(PPG!EndRound)          BY FairnessEnd
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, PTL DEF PPG!Spec, PPG!Fairness

\* Restatement in the base module's own vocabulary.
THEOREM RefinementOriginal == Spec => PropagationPassGraphRefinement
  BY Refinement DEF PropagationPassGraphRefinement

====
