---- MODULE BisectionFromBudget_Proof ----
(***************************************************************************
  Proof that the Budget<Probes>, cursor-pair, and projection construction
  refines Bisection, including its weak-fairness condition.

  SafetyRefinement maps initialization and each construction step to the
  target. FairnessTransfer uses WidthExpBound to show that the Budget guard
  cannot disable a live probe, then transfers enabledness and non-stuttering
  probe actions pointwise.

  The safety fragment assumes the declared domain and threshold types. The
  fairness fragment additionally assumes DomainSize <= Pow2[MaxProbes]. The
  held glue is the CF-002 cursor pair {lo, hi}; probes_taken is Budget
  allocation and Mid is a CF-001 projection.
 ***************************************************************************)
EXTENDS BisectionFromBudget, Naturals, NaturalsInduction, TLAPS

ASSUME DomainSizeAss == DomainSize \in Nat /\ DomainSize >= 2
ASSUME ThresholdAss == Threshold \in 1..(DomainSize - 1)
ASSUME MaxProbesAss == MaxProbes \in Nat

Inv == TypeInvariant

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1> QED BY DomainSizeAss, ThresholdAss, MaxProbesAss
         DEF Init, Inv, TypeInvariant

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1>c. /\ lo \in 0..DomainSize
        /\ hi \in 0..DomainSize
        /\ b_capacity = MaxProbes
        /\ b_allocated \in 0..MaxProbes
        /\ b_reserved = 0
        /\ b_pending = 0
    BY DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    BY <1>0, <1>c DEF Inv, vars, TypeInvariant
  <1>1. CASE ProbeLeft
    <2>a. /\ hi - lo >= 2
          /\ Mid >= Threshold
          /\ b_allocated + b_reserved + b_pending + 1 <= b_capacity
          /\ hi' = Mid
          /\ lo' = lo
          /\ b_allocated' = b_allocated + 1
          /\ UNCHANGED <<b_capacity, b_reserved, b_pending>>
      BY <1>1 DEF ProbeLeft
    <2>1. hi' \in 0..DomainSize
      BY <2>a, <1>c, DomainSizeAss DEF Mid
    <2>2. b_allocated' \in 0..MaxProbes
      BY <2>a, <1>c, MaxProbesAss
    <2> QED BY <2>a, <2>1, <2>2, <1>c DEF Inv, TypeInvariant
  <1>2. CASE ProbeRight
    <2>a. /\ hi - lo >= 2
          /\ Mid < Threshold
          /\ b_allocated + b_reserved + b_pending + 1 <= b_capacity
          /\ lo' = Mid + 1
          /\ hi' = hi
          /\ b_allocated' = b_allocated + 1
          /\ UNCHANGED <<b_capacity, b_reserved, b_pending>>
      BY <1>2 DEF ProbeRight
    <2>1. lo' \in 0..DomainSize
      BY <2>a, <1>c, DomainSizeAss, ThresholdAss DEF Mid
    <2>2. b_allocated' \in 0..MaxProbes
      BY <2>a, <1>c, MaxProbesAss
    <2> QED BY <2>a, <2>1, <2>2, <1>c DEF Inv, TypeInvariant
  <1>3. CASE Converged
    BY <1>3, <1>c DEF Converged, Inv, vars, TypeInvariant
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF Next

(*-------------------------------------------------------------------------*)
(* Safety: the inductive invariant holds in every reachable state.         *)
(*-------------------------------------------------------------------------*)
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv
    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'
    BY NextInv
  <1> QED BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM BudgetSafetySafety == Spec => []BudgetSafety
  <1>1. Inv => BudgetSafety
    BY MaxProbesAss
       DEF Inv, TypeInvariant, BudgetSafety, Bgt!SafetyInvariant
  <1> QED BY Safety, <1>1, PTL

(*-------------------------------------------------------------------------*)
(* The refinement, safety fragment: Init maps to B!Init, every step maps   *)
(* to a B step or a B stutter.                                             *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => B!Init
  BY DEF Init, B!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [B!Next]_(B!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [B!Next]_(B!vars)
    OBVIOUS
  <1>c. /\ lo \in 0..DomainSize
        /\ hi \in 0..DomainSize
        /\ b_capacity = MaxProbes
        /\ b_allocated \in 0..MaxProbes
        /\ b_reserved = 0
        /\ b_pending = 0
    BY DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    <2>1. UNCHANGED <<lo, hi, b_allocated>>
      BY <1>0 DEF vars
    <2> QED BY <2>1 DEF B!vars
  <1>1. CASE ProbeLeft
    <2>a. /\ hi - lo >= 2
          /\ Mid >= Threshold
          /\ hi' = Mid
          /\ lo' = lo
          /\ b_allocated' = b_allocated + 1
      BY <1>1 DEF ProbeLeft
    <2>1. B!ProbeLeft
      BY <2>a DEF B!ProbeLeft, B!Mid, Mid
    <2> QED BY <2>1 DEF B!Next
  <1>2. CASE ProbeRight
    <2>a. /\ hi - lo >= 2
          /\ Mid < Threshold
          /\ lo' = Mid + 1
          /\ hi' = hi
          /\ b_allocated' = b_allocated + 1
      BY <1>2 DEF ProbeRight
    <2>1. B!ProbeRight
      BY <2>a DEF B!ProbeRight, B!Mid, Mid
    <2> QED BY <2>1 DEF B!Next
  <1>3. CASE Converged
    <2>a. hi - lo < 2 /\ UNCHANGED vars
      BY <1>3 DEF Converged
    <2>1. B!Converged
      BY <2>a DEF B!Converged, B!vars, vars
    <2> QED BY <2>1 DEF B!Next
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF Next

(*-------------------------------------------------------------------------*)
(* Safety refinement, extended below with weak-fairness transfer.           *)
(*-------------------------------------------------------------------------*)
THEOREM SafetyRefinement == Spec => B!Init /\ [][B!Next]_(B!vars)
  <1>1. Init => B!Init
    BY InitRefines
  <1>2. Inv /\ [Next]_vars => [B!Next]_(B!vars)
    BY NextRefines
  <1>3. Spec => []Inv
    BY Safety
  <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec

(***************************************************************************
  Weak-fairness transfer. Pow2 and the interval-width strengthening establish
  Budget headroom; enabledness and action correspondence transfer the target
  fairness condition.
 ***************************************************************************)

\* Powers of two as a recursive function-fixpoint (represented as a function rather than an operator).
Pow2[k \in Nat] == IF k = 0 THEN 1 ELSE 2 * Pow2[k - 1]

\* The domain fits within MaxProbes halvings. Only the fairness layer uses
\* this premise.
ASSUME DomainFitsProbes == DomainSize <= Pow2[MaxProbes]

\* ---- Pow2 facts -----------------------------------------------------------
THEOREM Pow2DefConclusion == NatInductiveDefConclusion(Pow2, 1, LAMBDA v, n : 2 * v)
  <1>1. NatInductiveDefHypothesis(Pow2, 1, LAMBDA v, n : 2 * v)
    BY DEF NatInductiveDefHypothesis, Pow2
  <1> QED  BY <1>1, NatInductiveDef

LEMMA Pow2Def == \A k \in Nat : Pow2[k] = IF k = 0 THEN 1 ELSE 2 * Pow2[k - 1]
  BY Pow2DefConclusion DEF NatInductiveDefConclusion

LEMMA Pow2InNat == Pow2 \in [Nat -> Nat]
  <1>1. \A v \in Nat, n \in Nat \ {0} : 2 * v \in Nat
    OBVIOUS
  <1> QED  BY <1>1, NatInductiveDefType, Pow2DefConclusion

LEMMA Pow2Zero == Pow2[0] = 1
  BY Pow2Def

LEMMA Pow2Val == ASSUME NEW k \in Nat PROVE Pow2[k] \in Nat
  BY Pow2InNat

LEMMA Pow2HalfStep ==
  ASSUME NEW k \in Nat, k >= 1
  PROVE  Pow2[k] \div 2 = Pow2[k - 1]
  <1>1. k - 1 \in Nat
    OBVIOUS
  <1>2. Pow2[k - 1] \in Nat
    BY <1>1, Pow2Val
  <1>3. Pow2[k] = 2 * Pow2[k - 1]
    BY Pow2Def
  <1> QED  BY <1>2, <1>3

\* ---- Integer-division facts -----------------------------------------------
LEMMA DivHalfMono ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a <= b
  PROVE  a \div 2 <= b \div 2
  OBVIOUS

LEMMA MidFacts ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a <= b
  PROVE  /\ (a + b) \div 2 \in Nat
         /\ a <= (a + b) \div 2
         /\ (a + b) \div 2 <= b
         /\ (a + b) \div 2 - a = (b - a) \div 2
  OBVIOUS

LEMMA MidStrictFacts ==
  ASSUME NEW a \in Nat, NEW b \in Nat, b - a >= 2
  PROVE  /\ (a + b) \div 2 <= b - 1
         /\ b - ((a + b) \div 2 + 1) <= (b - a) \div 2
  OBVIOUS

LEMMA DivHalfLeSelf ==
  ASSUME NEW x \in Nat
  PROVE  x \div 2 \in Nat /\ x \div 2 <= x
  OBVIOUS

\* ---- The width-exponent strengthening -------------------------------------
\* The interval width is bounded by 2^(remaining probe budget), which makes
\* the budget guard non-binding while the interval is live.
WidthExpBound == hi - lo <= Pow2[MaxProbes - b_allocated]

InvL == Inv /\ WidthExpBound

LEMMA InitInvL == Init => InvL
  <1> SUFFICES ASSUME Init PROVE InvL
    OBVIOUS
  <1>1. Inv
    BY InitInv
  <1>2. WidthExpBound
    <2>0. b_allocated = 0
      BY DEF Init
    <2>1. MaxProbes - b_allocated = MaxProbes
      BY <2>0, MaxProbesAss
    <2>2. Pow2[MaxProbes - b_allocated] = Pow2[MaxProbes]
      BY <2>1
    <2>3. Pow2[MaxProbes] \in Nat
      BY MaxProbesAss, Pow2Val
    <2>4. hi - lo <= DomainSize
      BY DomainSizeAss, ThresholdAss DEF Init
    <2>5. hi - lo <= Pow2[MaxProbes - b_allocated]
      BY <2>2, <2>3, <2>4, DomainFitsProbes, DomainSizeAss, ThresholdAss DEF Init
    <2> QED BY <2>5 DEF WidthExpBound
  <1> QED BY <1>1, <1>2 DEF InvL

\* The enabledness bridge's arithmetic core: while the interval is live
\* (hi - lo >= 2), the width-exponent bound forces headroom in the probe
\* budget. This does not follow from the linear invariants alone.
LEMMA BudgetHeadroom ==
  InvL /\ hi - lo >= 2 => b_allocated + b_reserved + b_pending + 1 <= b_capacity
  <1> SUFFICES ASSUME InvL, hi - lo >= 2
               PROVE  b_allocated + b_reserved + b_pending + 1 <= b_capacity
    OBVIOUS
  <1>c. /\ lo \in 0..DomainSize
        /\ hi \in 0..DomainSize
        /\ b_capacity = MaxProbes
        /\ b_allocated \in 0..MaxProbes
        /\ b_reserved = 0
        /\ b_pending = 0
    BY DEF InvL, Inv, TypeInvariant
  <1>1. CASE b_allocated = MaxProbes
    <2>1. MaxProbes - b_allocated = 0
      BY <1>1, MaxProbesAss
    <2>2. Pow2[MaxProbes - b_allocated] = Pow2[0]
      BY <2>1
    <2>3. Pow2[MaxProbes - b_allocated] = 1
      BY <2>2, Pow2Zero
    <2>4. hi - lo <= 1
      BY <2>3 DEF InvL, WidthExpBound
    <2> QED BY <2>4, <1>c, DomainSizeAss
  <1>2. CASE b_allocated # MaxProbes
    BY <1>2, <1>c, MaxProbesAss
  <1> QED BY <1>1, <1>2

LEMMA NextInvL == InvL /\ [Next]_vars => InvL'
  <1> SUFFICES ASSUME InvL, [Next]_vars PROVE InvL'
    OBVIOUS
  <1>i. Inv'
    BY NextInv DEF InvL
  <1>c. /\ lo \in 0..DomainSize
        /\ hi \in 0..DomainSize
        /\ b_capacity = MaxProbes
        /\ b_allocated \in 0..MaxProbes
        /\ b_reserved = 0
        /\ b_pending = 0
    BY DEF InvL, Inv, TypeInvariant
  <1>nat. /\ lo \in Nat
          /\ hi \in Nat
          /\ b_allocated \in Nat
          /\ MaxProbes - b_allocated \in Nat
    BY <1>c, DomainSizeAss, MaxProbesAss
  <1>p2. Pow2[MaxProbes - b_allocated] \in Nat
    BY <1>nat, Pow2Val
  <1>wb. hi - lo <= Pow2[MaxProbes - b_allocated]
    BY DEF InvL, WidthExpBound
  <1>0. CASE UNCHANGED vars
    <2>1. hi' = hi /\ lo' = lo /\ b_allocated' = b_allocated
      BY <1>0 DEF vars
    <2>2. Pow2[MaxProbes - b_allocated'] = Pow2[MaxProbes - b_allocated]
      BY <2>1
    <2>3. WidthExpBound'
      BY <2>1, <2>2, <1>wb DEF WidthExpBound
    <2> QED BY <1>i, <2>3 DEF InvL
  <1>1. CASE ProbeLeft
    <2>a. /\ hi - lo >= 2
          /\ hi' = Mid
          /\ lo' = lo
          /\ b_allocated' = b_allocated + 1
      BY <1>1 DEF ProbeLeft
    <2>ord. lo <= hi
      BY <2>a, <1>nat
    <2>mid. /\ Mid \in Nat
            /\ lo <= Mid
            /\ Mid <= hi
            /\ Mid - lo = (hi - lo) \div 2
      BY <1>nat, <2>ord, MidFacts DEF Mid
    <2>w. /\ (hi - lo) \in Nat
          /\ (hi - lo) \div 2 \in Nat
          /\ (hi - lo) \div 2 <= hi - lo
      BY <1>nat, <2>ord, DivHalfLeSelf
    <2>hd. MaxProbes - b_allocated >= 1
      <3>1. b_allocated + b_reserved + b_pending + 1 <= b_capacity
        BY BudgetHeadroom, <2>a
      <3> QED BY <3>1, <1>c, MaxProbesAss
    <2>5. WidthExpBound'
      <3>pk. /\ Pow2[MaxProbes - b_allocated] \div 2 \in Nat
             /\ Pow2[(MaxProbes - b_allocated) - 1] \in Nat
        <4>1. (MaxProbes - b_allocated) - 1 \in Nat
          BY <2>hd, <1>nat
        <4> QED BY <1>p2, <4>1, DivHalfLeSelf, Pow2Val
      <3>1. hi' - lo' = (hi - lo) \div 2
        BY <2>a, <2>mid
      <3>4. (hi - lo) \div 2 <= Pow2[MaxProbes - b_allocated] \div 2
        BY <1>wb, <1>p2, <2>w, DivHalfMono
      <3>5. Pow2[MaxProbes - b_allocated] \div 2 = Pow2[(MaxProbes - b_allocated) - 1]
        BY <1>nat, <2>hd, Pow2HalfStep
      <3>6. Pow2[(MaxProbes - b_allocated) - 1] = Pow2[MaxProbes - b_allocated']
        <4>1. (MaxProbes - b_allocated) - 1 = MaxProbes - b_allocated'
          BY <2>a, <1>nat, MaxProbesAss
        <4> QED BY <4>1
      <3>7. hi' - lo' <= Pow2[MaxProbes - b_allocated']
        BY <3>1, <3>4, <3>5, <3>6, <2>w, <3>pk
      <3> QED BY <3>7 DEF WidthExpBound
    <2> QED BY <1>i, <2>5 DEF InvL
  <1>2. CASE ProbeRight
    <2>a. /\ hi - lo >= 2
          /\ lo' = Mid + 1
          /\ hi' = hi
          /\ b_allocated' = b_allocated + 1
      BY <1>2 DEF ProbeRight
    <2>ord. lo <= hi
      BY <2>a, <1>nat
    <2>mids. /\ Mid <= hi - 1
             /\ hi - (Mid + 1) <= (hi - lo) \div 2
      BY <1>nat, <2>a, MidStrictFacts DEF Mid
    <2>w. /\ (hi - lo) \in Nat
          /\ (hi - lo) \div 2 \in Nat
          /\ (hi - lo) \div 2 <= hi - lo
      BY <1>nat, <2>ord, DivHalfLeSelf
    <2>hd. MaxProbes - b_allocated >= 1
      <3>1. b_allocated + b_reserved + b_pending + 1 <= b_capacity
        BY BudgetHeadroom, <2>a
      <3> QED BY <3>1, <1>c, MaxProbesAss
    <2>5. WidthExpBound'
      <3>pk. /\ Pow2[MaxProbes - b_allocated] \div 2 \in Nat
             /\ Pow2[(MaxProbes - b_allocated) - 1] \in Nat
        <4>1. (MaxProbes - b_allocated) - 1 \in Nat
          BY <2>hd, <1>nat
        <4> QED BY <1>p2, <4>1, DivHalfLeSelf, Pow2Val
      <3>1. hi' - lo' <= (hi - lo) \div 2
        BY <2>a, <2>mids
      <3>4. (hi - lo) \div 2 <= Pow2[MaxProbes - b_allocated] \div 2
        BY <1>wb, <1>p2, <2>w, DivHalfMono
      <3>5. Pow2[MaxProbes - b_allocated] \div 2 = Pow2[(MaxProbes - b_allocated) - 1]
        BY <1>nat, <2>hd, Pow2HalfStep
      <3>6. Pow2[(MaxProbes - b_allocated) - 1] = Pow2[MaxProbes - b_allocated']
        <4>1. (MaxProbes - b_allocated) - 1 = MaxProbes - b_allocated'
          BY <2>a, <1>nat, MaxProbesAss
        <4> QED BY <4>1
      <3>7. hi' - lo' <= Pow2[MaxProbes - b_allocated']
        BY <3>1, <3>4, <3>5, <3>6, <2>w, <3>pk, <1>p2, <2>a, <2>mids, <1>nat
      <3> QED BY <3>7 DEF WidthExpBound
    <2> QED BY <1>i, <2>5 DEF InvL
  <1>3. CASE Converged
    <2>1. UNCHANGED vars
      BY <1>3 DEF Converged
    <2>2. hi' = hi /\ lo' = lo /\ b_allocated' = b_allocated
      BY <2>1 DEF vars
    <2>3. Pow2[MaxProbes - b_allocated'] = Pow2[MaxProbes - b_allocated]
      BY <2>2
    <2>4. WidthExpBound'
      BY <2>2, <2>3, <1>wb DEF WidthExpBound
    <2> QED BY <1>i, <2>4 DEF InvL
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF Next

THEOREM SafetyL == Spec => []InvL
  <1>1. Init => InvL
    BY InitInvL
  <1>2. InvL /\ [Next]_vars => InvL'
    BY NextInvL
  <1> QED BY <1>1, <1>2, PTL DEF Spec

\* ---- ENABLED correspondence -----------------------------------------------
\* Construction-side enabledness: while the interval is live, a probe is
\* enabled (the budget guard is discharged by BudgetHeadroom). ENABLED does
\* not distribute over \/ automatically, so the proof first rewrites the
\* decorated disjunction and then applies ENABLEDaxioms. ExpandENABLED uses
\* SMT to construct the tuple-valued next-state witness.
LEMMA ConstructionEnabled ==
  InvL /\ hi - lo >= 2 => ENABLED <<ProbeLeft \/ ProbeRight>>_vars
  <1> SUFFICES ASSUME InvL, hi - lo >= 2
               PROVE  ENABLED <<ProbeLeft \/ ProbeRight>>_vars
    OBVIOUS
  <1>c. /\ lo \in 0..DomainSize
        /\ hi \in 0..DomainSize
        /\ b_capacity = MaxProbes
        /\ b_allocated \in 0..MaxProbes
        /\ b_reserved = 0
        /\ b_pending = 0
    BY DEF InvL, Inv, TypeInvariant
  <1>nat. /\ lo \in Nat
          /\ hi \in Nat
          /\ lo <= hi
          /\ Mid \in Nat
          /\ lo <= Mid
          /\ Mid <= hi
          /\ b_allocated \in Nat
    BY <1>c, DomainSizeAss, MaxProbesAss, MidFacts DEF Mid
  <1>bud. b_allocated + b_reserved + b_pending + 1 <= b_capacity
    BY BudgetHeadroom
  <1>eq. <<ProbeLeft \/ ProbeRight>>_vars <=> <<ProbeLeft>>_vars \/ <<ProbeRight>>_vars
    BY DEF vars
  <1>dist. ENABLED <<ProbeLeft \/ ProbeRight>>_vars
             <=> ENABLED <<ProbeLeft>>_vars \/ ENABLED <<ProbeRight>>_vars
    <2>1. ENABLED <<ProbeLeft \/ ProbeRight>>_vars
            <=> ENABLED (<<ProbeLeft>>_vars \/ <<ProbeRight>>_vars)
      BY <1>eq, ENABLEDrules
    <2>2. ENABLED (<<ProbeLeft>>_vars \/ <<ProbeRight>>_vars)
            <=> ENABLED <<ProbeLeft>>_vars \/ ENABLED <<ProbeRight>>_vars
      BY ENABLEDaxioms
    <2> QED BY <2>1, <2>2
  <1>A. CASE Mid >= Threshold
    <2>1. ENABLED <<ProbeLeft>>_vars
      BY <1>A, <1>nat, <1>c, <1>bud, ExpandENABLED, SMT DEF ProbeLeft, Mid, vars
    <2> QED BY <2>1, <1>dist
  <1>B. CASE Mid < Threshold
    <2>1. ENABLED <<ProbeRight>>_vars
      BY <1>B, <1>nat, <1>c, <1>bud, ExpandENABLED, SMT DEF ProbeRight, Mid, vars
    <2> QED BY <2>1, <1>dist
  <1>trich. Mid >= Threshold \/ Mid < Threshold
    BY <1>nat, ThresholdAss
  <1> QED BY <1>A, <1>B, <1>trich

\* Target-side enabledness extracts the live-interval guard: any witness for
\* a target probe carries hi - lo >= 2.
LEMMA TargetEnabledGuard ==
  ENABLED <<B!ProbeLeft \/ B!ProbeRight>>_(B!vars) => hi - lo >= 2
  <1>eq. <<B!ProbeLeft \/ B!ProbeRight>>_(B!vars)
           <=> <<B!ProbeLeft>>_(B!vars) \/ <<B!ProbeRight>>_(B!vars)
    BY DEF B!vars
  <1>dist. ENABLED <<B!ProbeLeft \/ B!ProbeRight>>_(B!vars)
             <=> ENABLED <<B!ProbeLeft>>_(B!vars) \/ ENABLED <<B!ProbeRight>>_(B!vars)
    <2>1. ENABLED <<B!ProbeLeft \/ B!ProbeRight>>_(B!vars)
            <=> ENABLED (<<B!ProbeLeft>>_(B!vars) \/ <<B!ProbeRight>>_(B!vars))
      BY <1>eq, ENABLEDrules
    <2>2. ENABLED (<<B!ProbeLeft>>_(B!vars) \/ <<B!ProbeRight>>_(B!vars))
            <=> ENABLED <<B!ProbeLeft>>_(B!vars) \/ ENABLED <<B!ProbeRight>>_(B!vars)
      BY ENABLEDaxioms
    <2> QED BY <2>1, <2>2
  <1>L. ENABLED <<B!ProbeLeft>>_(B!vars) => hi - lo >= 2
    BY ExpandENABLED, SMT DEF B!ProbeLeft, B!Mid, B!vars
  <1>R. ENABLED <<B!ProbeRight>>_(B!vars) => hi - lo >= 2
    BY ExpandENABLED, SMT DEF B!ProbeRight, B!Mid, B!vars
  <1> QED BY <1>dist, <1>L, <1>R

\* Target-enabled implies construction-enabled: the two sides' probes are
\* enabled under exactly the same state condition once the invariant holds.
LEMMA EnabledTransfer ==
  InvL => (ENABLED <<B!ProbeLeft \/ B!ProbeRight>>_(B!vars)
             => ENABLED <<ProbeLeft \/ ProbeRight>>_vars)
  BY TargetEnabledGuard, ConstructionEnabled

\* Every construction probe step is a non-stuttering target probe step (the
\* Budget allocation strictly increases, and it is a target variable).
LEMMA ActionTransfer ==
  Inv /\ <<ProbeLeft \/ ProbeRight>>_vars => <<B!ProbeLeft \/ B!ProbeRight>>_(B!vars)
  <1> SUFFICES ASSUME Inv, <<ProbeLeft \/ ProbeRight>>_vars
               PROVE  <<B!ProbeLeft \/ B!ProbeRight>>_(B!vars)
    OBVIOUS
  <1>c. b_allocated \in 0..MaxProbes
    BY DEF Inv, TypeInvariant
  <1>1. CASE ProbeLeft
    <2>a. /\ hi - lo >= 2
          /\ Mid >= Threshold
          /\ hi' = Mid
          /\ lo' = lo
          /\ b_allocated' = b_allocated + 1
      BY <1>1 DEF ProbeLeft
    <2>1. B!ProbeLeft
      BY <2>a DEF B!ProbeLeft, B!Mid, Mid
    <2>2. B!vars' # B!vars
      BY <2>a, <1>c, MaxProbesAss DEF B!vars
    <2> QED BY <2>1, <2>2
  <1>2. CASE ProbeRight
    <2>a. /\ hi - lo >= 2
          /\ Mid < Threshold
          /\ lo' = Mid + 1
          /\ hi' = hi
          /\ b_allocated' = b_allocated + 1
      BY <1>2 DEF ProbeRight
    <2>1. B!ProbeRight
      BY <2>a DEF B!ProbeRight, B!Mid, Mid
    <2>2. B!vars' # B!vars
      BY <2>a, <1>c, MaxProbesAss DEF B!vars
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>1, <1>2

\* ---- The fairness transfer ------------------------------------------------
\* Pointwise, no WF1: with []InvL along every behaviour, (a) infinitely many
\* construction probes give infinitely many target probes (ActionTransfer),
\* and (b) infinitely-often-disabled construction probes give
\* infinitely-often-disabled target probes (EnabledTransfer,
\* contrapositive). PTL assembles the two cases through the WF
\* characterization on both sides.
THEOREM FairnessTransfer == Spec => WF_(B!vars)(B!ProbeLeft \/ B!ProbeRight)
  <1>1. Spec => []InvL
    BY SafetyL
  <1>2. InvL /\ <<ProbeLeft \/ ProbeRight>>_vars
          => <<B!ProbeLeft \/ B!ProbeRight>>_(B!vars)
    BY ActionTransfer DEF InvL
  <1>3. InvL => (ENABLED <<B!ProbeLeft \/ B!ProbeRight>>_(B!vars)
                   => ENABLED <<ProbeLeft \/ ProbeRight>>_vars)
    BY EnabledTransfer
  <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec

(*-------------------------------------------------------------------------*)
(* The full refinement: safety fragment + WF transfer.                     *)
(*-------------------------------------------------------------------------*)
THEOREM Refinement == Spec => B!Spec
  <1>1. Init => B!Init
    BY InitRefines
  <1>2. Inv /\ [Next]_vars => [B!Next]_(B!vars)
    BY NextRefines
  <1>3. Spec => []Inv
    BY Safety
  <1>4. Spec => WF_(B!vars)(B!ProbeLeft \/ B!ProbeRight)
    BY FairnessTransfer
  <1> QED BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec, B!Spec

\* Restatement in the construction module's public vocabulary.
THEOREM RefinementOriginal == Spec => BRefinement
  BY Refinement DEF BRefinement

====
