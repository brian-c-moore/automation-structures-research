---- MODULE EquivalenceClassFromRegistry_Proof ----
(***************************************************************************
  Parametric TLAPS proof of the registry-and-budget construction's refinement
  to EquivalenceClass.

  Discharges, unbounded and parametric:

      Refinement == Spec => EC!Spec

  Every behavior of the two-ResourceRegistry, Budget, and defaulted-view
  construction is an EquivalenceClass behavior under the stated mapping. The
  proof also establishes TypeSafety, ParentUniqueSafety, RankUniqueSafety, and
  BudgetSafetyPreservation. The uniqueness proofs require no finiteness
  assumption on Elements because each value set is empty or a singleton.

  Proof structure:
    (i)  the RepFun recursive-fold idioms of EquivalenceClass_Proof.tla
         (FiniteNatInductiveDef recovery of the recursion equation, the
         per-application unfolding lemma, NatInduction over the hop
         budget) -- applied twice, to the construction's RepFunC and to
         the instance-substituted EC!RepFun, then joined by the pointwise
         agreement lemma RepPointwise (both are fixpoints of the same
         recursion over the same defaulted parent view);
    (ii) CHOOSE-determinacy over UniqueMapping: the defaulted-view
         projections are well-defined because each key holds at most one
         stored value (functional-form uniqueness InvPU/InvRU), which
         pins the bounded CHOOSE in PView/RView to the stored value
         (PViewEntry/RViewEntry);
    (iii) the registry-set-to-function bridge: Register's Upsert on the
         entry set maps to an EXCEPT update of the defaulted view
         (PViewUpsert/RViewUpsert), proved over a generic set S so the
         same lemma serves the primed and unprimed states.

  The one inductive strengthening beyond typing + uniqueness is
  RankOpsBoundC (every view rank is at most the Budget allocation -- the
  RankOpsBound shape from the base proof), which keeps the equal-rank
  merge's incremented rank inside RankValues.

  Parametric boundary: Elements is an arbitrary set (possibly empty; no
  cardinality or finiteness is used anywhere); MaxOps \in Nat.

  State boundary: every variable belongs to a retained component;
  MapParent, MapRnk, and RepC are derived defaulted views and a fold.
 ***************************************************************************)
EXTENDS EquivalenceClassFromRegistry, Naturals, NaturalsInduction,
        FiniteSetTheorems, TLAPS

ASSUME MaxOpsAss == MaxOps \in Nat

(*-------------------------------------------------------------------------*)
(* Generic defaulted views over an arbitrary entry set S, with the         *)
(* functional-form uniqueness predicates. Stated over a generic S so one   *)
(* lemma serves both the unprimed and primed registry states.              *)
(*-------------------------------------------------------------------------*)
PUniqueOf(S) == \A k \in Elements : \A v1, v2 \in Elements :
                    (<<k, v1>> \in S /\ <<k, v2>> \in S) => v1 = v2
RUniqueOf(S) == \A k \in Elements : \A v1, v2 \in RankValues :
                    (<<k, v1>> \in S /\ <<k, v2>> \in S) => v1 = v2

PView(S) == [e \in Elements |->
                IF \E v \in Elements : <<e, v>> \in S
                THEN CHOOSE v \in Elements : <<e, v>> \in S
                ELSE e]
RView(S) == [e \in Elements |->
                IF \E v \in RankValues : <<e, v>> \in S
                THEN CHOOSE v \in RankValues : <<e, v>> \in S
                ELSE 0]

LEMMA MapParentIsPView == MapParent = PView(p_entries)
  BY DEF MapParent, PView

LEMMA MapRnkIsRView == MapRnk = RView(r_entries)
  BY DEF MapRnk, RView

LEMMA PViewType == ASSUME NEW S, NEW e \in Elements
                   PROVE  PView(S)[e] \in Elements
  <1>1. CASE \E v \in Elements : <<e, v>> \in S
    <2>1. (CHOOSE v \in Elements : <<e, v>> \in S) \in Elements
      BY <1>1
    <2> QED BY <1>1, <2>1 DEF PView
  <1>2. CASE ~\E v \in Elements : <<e, v>> \in S
    BY <1>2 DEF PView
  <1> QED BY <1>1, <1>2

LEMMA RViewType == ASSUME NEW S, NEW e \in Elements
                   PROVE  RView(S)[e] \in RankValues
  <1>0. 0 \in RankValues
    BY MaxOpsAss DEF RankValues
  <1>1. CASE \E v \in RankValues : <<e, v>> \in S
    <2>1. (CHOOSE v \in RankValues : <<e, v>> \in S) \in RankValues
      BY <1>1
    <2> QED BY <1>1, <2>1 DEF RView
  <1>2. CASE ~\E v \in RankValues : <<e, v>> \in S
    BY <1>2, <1>0 DEF RView
  <1> QED BY <1>1, <1>2

LEMMA MapParentType == \A e \in Elements : MapParent[e] \in Elements
  BY MapParentIsPView, PViewType

LEMMA MapRnkType == \A e \in Elements : MapRnk[e] \in RankValues
  BY MapRnkIsRView, RViewType

\* CHOOSE-determinacy: with functional-form uniqueness, a stored entry pins
\* the defaulted view's value at its key.
LEMMA PViewEntry ==
  ASSUME NEW S, PUniqueOf(S),
         NEW e \in Elements, NEW v \in Elements, <<e, v>> \in S
  PROVE  PView(S)[e] = v
  <1>ex. \E w \in Elements : <<e, w>> \in S
    OBVIOUS
  <1>ch. /\ (CHOOSE w \in Elements : <<e, w>> \in S) \in Elements
         /\ <<e, (CHOOSE w \in Elements : <<e, w>> \in S)>> \in S
    BY <1>ex
  <1>eq. (CHOOSE w \in Elements : <<e, w>> \in S) = v
    BY <1>ch DEF PUniqueOf
  <1> QED BY <1>ex, <1>eq DEF PView

LEMMA RViewEntry ==
  ASSUME NEW S, RUniqueOf(S),
         NEW e \in Elements, NEW v \in RankValues, <<e, v>> \in S
  PROVE  RView(S)[e] = v
  <1>ex. \E w \in RankValues : <<e, w>> \in S
    OBVIOUS
  <1>ch. /\ (CHOOSE w \in RankValues : <<e, w>> \in S) \in RankValues
         /\ <<e, (CHOOSE w \in RankValues : <<e, w>> \in S)>> \in S
    BY <1>ex
  <1>eq. (CHOOSE w \in RankValues : <<e, w>> \in S) = v
    BY <1>ch DEF RUniqueOf
  <1> QED BY <1>ex, <1>eq DEF RView

LEMMA PViewNoEntry ==
  ASSUME NEW S, NEW e \in Elements, ~\E v \in Elements : <<e, v>> \in S
  PROVE  PView(S)[e] = e
  BY DEF PView

LEMMA RViewNoEntry ==
  ASSUME NEW S, NEW e \in Elements, ~\E v \in RankValues : <<e, v>> \in S
  PROVE  RView(S)[e] = 0
  BY DEF RView

LEMMA PViewEmpty == PView({}) = [e \in Elements |-> e]
  <1>1. \A e \in Elements : PView({})[e] = e
    BY PViewNoEntry
  <1> QED BY <1>1 DEF PView

LEMMA RViewEmpty == RView({}) = [e \in Elements |-> 0]
  <1>1. \A e \in Elements : RView({})[e] = 0
    BY RViewNoEntry
  <1> QED BY <1>1 DEF RView

\* Upsert preserves functional-form uniqueness over a generic entry set.
LEMMA UpsertPreservesPUnique ==
  ASSUME NEW S, PUniqueOf(S), NEW k \in Elements, NEW v \in Elements
  PROVE  PUniqueOf(Upsert(S, k, v))
  <1> SUFFICES ASSUME NEW key \in Elements,
                      NEW v1 \in Elements, NEW v2 \in Elements,
                      <<key, v1>> \in Upsert(S, k, v),
                      <<key, v2>> \in Upsert(S, k, v)
               PROVE  v1 = v2
    BY DEF PUniqueOf
  <1>mem. \A w \in Elements : <<key, w>> \in Upsert(S, k, v) =>
              (key /= k /\ <<key, w>> \in S) \/ (key = k /\ w = v)
    BY DEF Upsert
  <1>A. CASE key = k
    BY <1>A, <1>mem
  <1>B. CASE key /= k
    BY <1>B, <1>mem DEF PUniqueOf
  <1> QED BY <1>A, <1>B

LEMMA UpsertPreservesRUnique ==
  ASSUME NEW S, RUniqueOf(S), NEW k \in Elements, NEW v \in RankValues
  PROVE  RUniqueOf(Upsert(S, k, v))
  <1> SUFFICES ASSUME NEW key \in Elements,
                      NEW v1 \in RankValues, NEW v2 \in RankValues,
                      <<key, v1>> \in Upsert(S, k, v),
                      <<key, v2>> \in Upsert(S, k, v)
               PROVE  v1 = v2
    BY DEF RUniqueOf
  <1>mem. \A w \in RankValues : <<key, w>> \in Upsert(S, k, v) =>
              (key /= k /\ <<key, w>> \in S) \/ (key = k /\ w = v)
    BY DEF Upsert
  <1>A. CASE key = k
    BY <1>A, <1>mem
  <1>B. CASE key /= k
    BY <1>B, <1>mem DEF RUniqueOf
  <1> QED BY <1>A, <1>B

\* The registry-set-to-function bridge: Register's Upsert on the entry set
\* is an EXCEPT update of the defaulted view.
LEMMA PViewUpsert ==
  ASSUME NEW S, PUniqueOf(S), NEW k \in Elements, NEW v \in Elements
  PROVE  PView(Upsert(S, k, v)) = [PView(S) EXCEPT ![k] = v]
  <1>U. PUniqueOf(Upsert(S, k, v))
    BY UpsertPreservesPUnique
  <1>k. PView(Upsert(S, k, v))[k] = v
    <2>1. <<k, v>> \in Upsert(S, k, v)
      BY DEF Upsert
    <2> QED BY <1>U, <2>1, PViewEntry
  <1>o. ASSUME NEW e \in Elements, e /= k
        PROVE  PView(Upsert(S, k, v))[e] = PView(S)[e]
    <2>mem. \A w \in Elements : <<e, w>> \in Upsert(S, k, v) <=> <<e, w>> \in S
      BY <1>o DEF Upsert
    <2>A. CASE \E w \in Elements : <<e, w>> \in S
      <3>1. PICK w0 \in Elements : <<e, w0>> \in S
        BY <2>A
      <3>2. PView(S)[e] = w0
        BY <3>1, PViewEntry
      <3>3. <<e, w0>> \in Upsert(S, k, v)
        BY <2>mem, <3>1
      <3>4. PView(Upsert(S, k, v))[e] = w0
        BY <1>U, <3>3, PViewEntry
      <3> QED BY <3>2, <3>4
    <2>B. CASE ~\E w \in Elements : <<e, w>> \in S
      <3>1. ~\E w \in Elements : <<e, w>> \in Upsert(S, k, v)
        BY <2>B, <2>mem
      <3>2. PView(Upsert(S, k, v))[e] = e
        BY <3>1, PViewNoEntry
      <3>3. PView(S)[e] = e
        BY <2>B, PViewNoEntry
      <3> QED BY <3>2, <3>3
    <2> QED BY <2>A, <2>B
  <1>ptw. \A e \in Elements :
            PView(Upsert(S, k, v))[e] = [PView(S) EXCEPT ![k] = v][e]
    <2>1. [PView(S) EXCEPT ![k] = v][k] = v
      BY DEF PView
    <2>2. \A e \in Elements : e /= k =>
              [PView(S) EXCEPT ![k] = v][e] = PView(S)[e]
      BY DEF PView
    <2> QED BY <1>k, <1>o, <2>1, <2>2
  <1> QED BY <1>ptw DEF PView

LEMMA RViewUpsert ==
  ASSUME NEW S, RUniqueOf(S), NEW k \in Elements, NEW v \in RankValues
  PROVE  RView(Upsert(S, k, v)) = [RView(S) EXCEPT ![k] = v]
  <1>U. RUniqueOf(Upsert(S, k, v))
    BY UpsertPreservesRUnique
  <1>k. RView(Upsert(S, k, v))[k] = v
    <2>1. <<k, v>> \in Upsert(S, k, v)
      BY DEF Upsert
    <2> QED BY <1>U, <2>1, RViewEntry
  <1>o. ASSUME NEW e \in Elements, e /= k
        PROVE  RView(Upsert(S, k, v))[e] = RView(S)[e]
    <2>mem. \A w \in RankValues : <<e, w>> \in Upsert(S, k, v) <=> <<e, w>> \in S
      BY <1>o DEF Upsert
    <2>A. CASE \E w \in RankValues : <<e, w>> \in S
      <3>1. PICK w0 \in RankValues : <<e, w0>> \in S
        BY <2>A
      <3>2. RView(S)[e] = w0
        BY <3>1, RViewEntry
      <3>3. <<e, w0>> \in Upsert(S, k, v)
        BY <2>mem, <3>1
      <3>4. RView(Upsert(S, k, v))[e] = w0
        BY <1>U, <3>3, RViewEntry
      <3> QED BY <3>2, <3>4
    <2>B. CASE ~\E w \in RankValues : <<e, w>> \in S
      <3>1. ~\E w \in RankValues : <<e, w>> \in Upsert(S, k, v)
        BY <2>B, <2>mem
      <3>2. RView(Upsert(S, k, v))[e] = 0
        BY <3>1, RViewNoEntry
      <3>3. RView(S)[e] = 0
        BY <2>B, RViewNoEntry
      <3> QED BY <3>2, <3>3
    <2> QED BY <2>A, <2>B
  <1>ptw. \A e \in Elements :
            RView(Upsert(S, k, v))[e] = [RView(S) EXCEPT ![k] = v][e]
    <2>1. [RView(S) EXCEPT ![k] = v][k] = v
      BY DEF RView
    <2>2. \A e \in Elements : e /= k =>
              [RView(S) EXCEPT ![k] = v][e] = RView(S)[e]
      BY DEF RView
    <2> QED BY <1>k, <1>o, <2>1, <2>2
  <1> QED BY <1>ptw DEF RView

(*-------------------------------------------------------------------------*)
(* The RepFun agreement: the construction's RepFunC and the instance's     *)
(* EC!RepFun are fixpoints of the SAME recursion over the same defaulted   *)
(* parent view, so they agree pointwise (EquivalenceClass_Proof's          *)
(* FiniteNatInductiveDef + RepFunApp + NatInduction idioms, applied to     *)
(* both fixpoints and joined).                                             *)
(*-------------------------------------------------------------------------*)
RepStepC(prev) == [e \in Elements |-> IF MapParent[e] = e THEN e
                                      ELSE prev[MapParent[e]]]

LEMMA RepFunCDefConclusion ==
  FiniteNatInductiveDefConclusion(RepFunC, [e \in Elements |-> e],
                                  LAMBDA prev, k : RepStepC(prev), 0, MaxOps + 1)
  <1>1. FiniteNatInductiveDefHypothesis(RepFunC, [e \in Elements |-> e],
                                        LAMBDA prev, k : RepStepC(prev), 0, MaxOps + 1)
    BY DEF FiniteNatInductiveDefHypothesis, RepFunC, RepStepC
  <1>2. MaxOps + 1 \in Nat
    BY MaxOpsAss
  <1> QED  BY <1>1, <1>2, FiniteNatInductiveDef

LEMMA RepFunCApp ==
  ASSUME NEW k \in 0..(MaxOps + 1), NEW e \in Elements
  PROVE  RepFunC[k][e] = IF k = 0 THEN e
                         ELSE IF MapParent[e] = e THEN e
                              ELSE RepFunC[k - 1][MapParent[e]]
  <1>1. RepFunC[k] = IF k = 0 THEN [x \in Elements |-> x]
                     ELSE RepStepC(RepFunC[k - 1])
    BY RepFunCDefConclusion DEF FiniteNatInductiveDefConclusion
  <1>2. CASE k = 0
    BY <1>1, <1>2
  <1>3. CASE k # 0
    <2>1. RepFunC[k] = RepStepC(RepFunC[k - 1])  BY <1>1, <1>3
    <2> QED  BY <2>1, <1>3 DEF RepStepC
  <1> QED  BY <1>2, <1>3

LEMMA ECRepFunDefConclusion ==
  FiniteNatInductiveDefConclusion(EC!RepFun, [e \in Elements |-> e],
                                  LAMBDA prev, k : RepStepC(prev), 0, MaxOps + 1)
  <1>1. FiniteNatInductiveDefHypothesis(EC!RepFun, [e \in Elements |-> e],
                                        LAMBDA prev, k : RepStepC(prev), 0, MaxOps + 1)
    BY DEF FiniteNatInductiveDefHypothesis, EC!RepFun, RepStepC
  <1>2. MaxOps + 1 \in Nat
    BY MaxOpsAss
  <1> QED  BY <1>1, <1>2, FiniteNatInductiveDef

LEMMA ECRepFunApp ==
  ASSUME NEW k \in 0..(MaxOps + 1), NEW e \in Elements
  PROVE  EC!RepFun[k][e] = IF k = 0 THEN e
                           ELSE IF MapParent[e] = e THEN e
                                ELSE EC!RepFun[k - 1][MapParent[e]]
  <1>1. EC!RepFun[k] = IF k = 0 THEN [x \in Elements |-> x]
                       ELSE RepStepC(EC!RepFun[k - 1])
    BY ECRepFunDefConclusion DEF FiniteNatInductiveDefConclusion
  <1>2. CASE k = 0
    BY <1>1, <1>2
  <1>3. CASE k # 0
    <2>1. EC!RepFun[k] = RepStepC(EC!RepFun[k - 1])  BY <1>1, <1>3
    <2> QED  BY <2>1, <1>3 DEF RepStepC
  <1> QED  BY <1>2, <1>3

LEMMA RepFunCType ==
  \A k \in 0..(MaxOps + 1) : \A e \in Elements : RepFunC[k][e] \in Elements
  <1> DEFINE Q(k) == k \in 0..(MaxOps + 1) =>
                       \A e \in Elements : RepFunC[k][e] \in Elements
  <1>1. Q(0)
    <2> SUFFICES ASSUME 0 \in 0..(MaxOps + 1), NEW e \in Elements
                 PROVE  RepFunC[0][e] \in Elements
      OBVIOUS
    <2> QED  BY RepFunCApp
  <1>2. ASSUME NEW k \in Nat, Q(k) PROVE Q(k + 1)
    <2> SUFFICES ASSUME k + 1 \in 0..(MaxOps + 1), NEW e \in Elements
                 PROVE  RepFunC[k + 1][e] \in Elements
      OBVIOUS
    <2>k. k \in 0..(MaxOps + 1)  BY MaxOpsAss
    <2>pe. MapParent[e] \in Elements  BY MapParentType
    <2>1. RepFunC[k + 1][e] = IF MapParent[e] = e THEN e
                              ELSE RepFunC[k][MapParent[e]]
      BY RepFunCApp, MaxOpsAss
    <2>2. RepFunC[k][MapParent[e]] \in Elements  BY <2>k, <2>pe, Q(k)
    <2> QED  BY <2>1, <2>2
  <1>3. \A k \in Nat : Q(k)  BY <1>1, <1>2, NatInduction
  <1> QED  BY <1>3, MaxOpsAss

LEMMA RepCType == \A e \in Elements : RepC(e) \in Elements
  <1>top. MaxOps + 1 \in 0..(MaxOps + 1)  BY MaxOpsAss
  <1> QED  BY <1>top, RepFunCType DEF RepC

LEMMA RepPointwise ==
  \A k \in 0..(MaxOps + 1) : \A e \in Elements : RepFunC[k][e] = EC!RepFun[k][e]
  <1> DEFINE Q(k) == k \in 0..(MaxOps + 1) =>
                       \A e \in Elements : RepFunC[k][e] = EC!RepFun[k][e]
  <1>1. Q(0)
    <2> SUFFICES ASSUME 0 \in 0..(MaxOps + 1), NEW e \in Elements
                 PROVE  RepFunC[0][e] = EC!RepFun[0][e]
      OBVIOUS
    <2> QED  BY RepFunCApp, ECRepFunApp
  <1>2. ASSUME NEW k \in Nat, Q(k) PROVE Q(k + 1)
    <2> SUFFICES ASSUME k + 1 \in 0..(MaxOps + 1), NEW e \in Elements
                 PROVE  RepFunC[k + 1][e] = EC!RepFun[k + 1][e]
      OBVIOUS
    <2>k. k \in 0..(MaxOps + 1)  BY MaxOpsAss
    <2>pe. MapParent[e] \in Elements  BY MapParentType
    <2>1. RepFunC[k + 1][e] = IF MapParent[e] = e THEN e
                              ELSE RepFunC[k][MapParent[e]]
      BY RepFunCApp, MaxOpsAss
    <2>2. EC!RepFun[k + 1][e] = IF MapParent[e] = e THEN e
                                ELSE EC!RepFun[k][MapParent[e]]
      BY ECRepFunApp, MaxOpsAss
    <2>3. RepFunC[k][MapParent[e]] = EC!RepFun[k][MapParent[e]]
      BY <2>k, <2>pe, Q(k)
    <2> QED  BY <2>1, <2>2, <2>3
  <1>3. \A k \in Nat : Q(k)  BY <1>1, <1>2, NatInduction
  <1> QED  BY <1>3, MaxOpsAss

LEMMA RepAgree == \A e \in Elements : RepC(e) = EC!Rep(e)
  <1>top. MaxOps + 1 \in 0..(MaxOps + 1)  BY MaxOpsAss
  <1> QED  BY <1>top, RepPointwise DEF RepC, EC!Rep

(*-------------------------------------------------------------------------*)
(* Inductive invariant: typing + functional-form uniqueness of both        *)
(* registries + the rank/ops bound that keeps the equal-rank merge's       *)
(* incremented rank inside RankValues.                                     *)
(*-------------------------------------------------------------------------*)
InvPU == PUniqueOf(p_entries)
InvRU == RUniqueOf(r_entries)
RankOpsBoundC == \A e \in Elements : MapRnk[e] <= b_allocated

Inv == TypeInvariant /\ InvPU /\ InvRU /\ RankOpsBoundC

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY MaxOpsAss DEF Init, TypeInvariant
  <1>2. InvPU
    BY DEF Init, InvPU, PUniqueOf
  <1>3. InvRU
    BY DEF Init, InvRU, RUniqueOf
  <1>4. RankOpsBoundC
    <2>1. \A e \in Elements : MapRnk[e] = 0
      BY DEF Init, MapRnk
    <2>2. b_allocated = 0
      BY DEF Init
    <2> QED BY <2>1, <2>2 DEF RankOpsBoundC
  <1> QED BY <1>1, <1>2, <1>3, <1>4 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1>c. /\ p_entries \subseteq (Elements \X Elements)
        /\ r_entries \subseteq (Elements \X RankValues)
        /\ b_capacity = MaxOps
        /\ b_allocated \in 0..MaxOps
        /\ b_reserved = 0
        /\ b_pending = 0
    BY DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    <2>1. /\ p_entries' = p_entries
          /\ r_entries' = r_entries
          /\ b_capacity' = b_capacity
          /\ b_allocated' = b_allocated
          /\ b_reserved' = b_reserved
          /\ b_pending' = b_pending
      BY <1>0 DEF vars
    <2>2. MapRnk' = MapRnk
      BY <2>1 DEF MapRnk
    <2> QED BY <2>1, <2>2, <1>c
       DEF Inv, TypeInvariant, InvPU, InvRU, RankOpsBoundC, PUniqueOf, RUniqueOf
  <1>1. CASE \E a \in Elements, b \in Elements : UnionStep(a, b)
    <2> SUFFICES ASSUME NEW a \in Elements, NEW b \in Elements, UnionStep(a, b)
                 PROVE  Inv'
      BY <1>1
    <2> DEFINE ra == RepC(a)
    <2> DEFINE rb == RepC(b)
    <2>raE. ra \in Elements  BY RepCType
    <2>rbE. rb \in Elements  BY RepCType
    <2>rnkNat. MapRnk[ra] \in Nat /\ MapRnk[rb] \in Nat
      BY <2>raE, <2>rbE, MapRnkType, MaxOpsAss DEF RankValues
    <2>bud. b_allocated + b_reserved + b_pending + 1 <= b_capacity
      BY DEF UnionStep
    <2>opsP. b_allocated' = b_allocated + 1
      BY DEF UnionStep
    <2>unch. UNCHANGED <<b_capacity, b_reserved, b_pending>>
      BY DEF UnionStep
    <2>ops2. b_allocated < MaxOps
      BY <2>bud, <1>c, MaxOpsAss
    <2>tb. /\ b_capacity' = MaxOps
           /\ b_allocated' \in 0..MaxOps
           /\ b_reserved' = 0
           /\ b_pending' = 0
      BY <2>unch, <2>opsP, <2>ops2, <1>c, MaxOpsAss
    <2>rb1. \A e \in Elements : MapRnk[e] <= b_allocated
      BY DEF Inv, RankOpsBoundC
    <2>rbn. \A e \in Elements : MapRnk[e] \in Nat
      BY MapRnkType, MaxOpsAss DEF RankValues
    <2>c1. CASE MapRnk[ra] < MapRnk[rb]
      <3>pp. p_entries' = Upsert(p_entries, ra, rb)
        BY <2>c1 DEF UnionStep
      <3>rp. r_entries' = r_entries
        BY <2>c1 DEF UnionStep
      <3>1. p_entries' \subseteq (Elements \X Elements)
        BY <3>pp, <1>c, <2>raE, <2>rbE DEF Upsert
      <3>2. TypeInvariant'
        BY <3>1, <3>rp, <2>tb, <1>c DEF TypeInvariant
      <3>3. InvPU'
        BY <3>pp, <2>raE, <2>rbE, UpsertPreservesPUnique DEF Inv, InvPU
      <3>4. InvRU'
        BY <3>rp DEF Inv, InvRU, RUniqueOf
      <3>5. RankOpsBoundC'
        <4>1. MapRnk' = MapRnk
          BY <3>rp DEF MapRnk
        <4> QED BY <4>1, <2>rb1, <2>rbn, <2>opsP, <1>c, MaxOpsAss
           DEF RankOpsBoundC
      <3> QED BY <3>2, <3>3, <3>4, <3>5 DEF Inv
    <2>c2. CASE MapRnk[ra] > MapRnk[rb]
      <3>pp. p_entries' = Upsert(p_entries, rb, ra)
        BY <2>c2, <2>rnkNat DEF UnionStep
      <3>rp. r_entries' = r_entries
        BY <2>c2, <2>rnkNat DEF UnionStep
      <3>1. p_entries' \subseteq (Elements \X Elements)
        BY <3>pp, <1>c, <2>raE, <2>rbE DEF Upsert
      <3>2. TypeInvariant'
        BY <3>1, <3>rp, <2>tb, <1>c DEF TypeInvariant
      <3>3. InvPU'
        BY <3>pp, <2>raE, <2>rbE, UpsertPreservesPUnique DEF Inv, InvPU
      <3>4. InvRU'
        BY <3>rp DEF Inv, InvRU, RUniqueOf
      <3>5. RankOpsBoundC'
        <4>1. MapRnk' = MapRnk
          BY <3>rp DEF MapRnk
        <4> QED BY <4>1, <2>rb1, <2>rbn, <2>opsP, <1>c, MaxOpsAss
           DEF RankOpsBoundC
      <3> QED BY <3>2, <3>3, <3>4, <3>5 DEF Inv
    <2>c3. CASE MapRnk[ra] = MapRnk[rb]
      <3>pp. p_entries' = Upsert(p_entries, rb, ra)
        BY <2>c3, <2>rnkNat DEF UnionStep
      <3>rp. r_entries' = Upsert(r_entries, ra, MapRnk[ra] + 1)
        BY <2>c3, <2>rnkNat DEF UnionStep
      <3>rv. MapRnk[ra] + 1 \in RankValues
        <4>1. MapRnk[ra] <= b_allocated
          BY <2>raE, <2>rb1
        <4> QED BY <4>1, <2>ops2, <2>rnkNat, <1>c, MaxOpsAss DEF RankValues
      <3>1. p_entries' \subseteq (Elements \X Elements)
        BY <3>pp, <1>c, <2>raE, <2>rbE DEF Upsert
      <3>1r. r_entries' \subseteq (Elements \X RankValues)
        BY <3>rp, <1>c, <2>raE, <3>rv DEF Upsert
      <3>2. TypeInvariant'
        BY <3>1, <3>1r, <2>tb, <1>c DEF TypeInvariant
      <3>3. InvPU'
        BY <3>pp, <2>raE, <2>rbE, UpsertPreservesPUnique DEF Inv, InvPU
      <3>4. InvRU'
        BY <3>rp, <2>raE, <3>rv, UpsertPreservesRUnique DEF Inv, InvRU
      <3>5. RankOpsBoundC'
        <4>br. MapRnk' = [MapRnk EXCEPT ![ra] = MapRnk[ra] + 1]
          <5>1. MapRnk' = RView(r_entries')
            BY DEF MapRnk, RView
          <5>2. RView(Upsert(r_entries, ra, MapRnk[ra] + 1))
                  = [RView(r_entries) EXCEPT ![ra] = MapRnk[ra] + 1]
            BY <2>raE, <3>rv, RViewUpsert DEF Inv, InvRU
          <5> QED BY <5>1, <5>2, <3>rp, MapRnkIsRView
        <4>ptw. \A e \in Elements : MapRnk'[e] <= b_allocated'
          <5>1. \A e \in Elements :
                    MapRnk'[e] = IF e = ra THEN MapRnk[ra] + 1 ELSE MapRnk[e]
            BY <4>br, <2>raE DEF MapRnk
          <5>2. MapRnk[ra] + 1 <= b_allocated + 1
            BY <2>raE, <2>rb1, <2>rnkNat, <1>c, MaxOpsAss
          <5>3. \A e \in Elements : MapRnk[e] <= b_allocated + 1
            BY <2>rb1, <2>rbn, <1>c, MaxOpsAss
          <5> QED BY <5>1, <5>2, <5>3, <2>opsP
        <4> QED BY <4>ptw DEF RankOpsBoundC
      <3> QED BY <3>2, <3>3, <3>4, <3>5 DEF Inv
    <2> QED BY <2>c1, <2>c2, <2>c3, <2>rnkNat
  <1>2. CASE Idle
    <2>1. UNCHANGED vars
      BY <1>2 DEF Idle
    <2>2. /\ p_entries' = p_entries
          /\ r_entries' = r_entries
          /\ b_capacity' = b_capacity
          /\ b_allocated' = b_allocated
          /\ b_reserved' = b_reserved
          /\ b_pending' = b_pending
      BY <2>1 DEF vars
    <2>3. MapRnk' = MapRnk
      BY <2>2 DEF MapRnk
    <2> QED BY <2>2, <2>3, <1>c
       DEF Inv, TypeInvariant, InvPU, InvRU, RankOpsBoundC, PUniqueOf, RUniqueOf
  <1> QED BY <1>0, <1>1, <1>2 DEF Next

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

THEOREM BudgetSafetyPreservation == Spec => []BudgetSafety
  <1>1. Inv => BudgetSafety
    BY MaxOpsAss
       DEF Inv, TypeInvariant, BudgetSafety, Bgt!SafetyInvariant
  <1> QED BY Safety, <1>1, PTL

\* Registry Cardinality-form uniqueness follows from functional uniqueness.
\* The instantiated Cardinality symbols expand to this module's closed
\* FiniteSets definition. Each key's value set is empty or a singleton, so
\* FS_EmptySet and FS_Singleton supply the needed finiteness facts.
LEMMA PCardinalityBridge == \A T : PReg!Cardinality(T) = Cardinality(T)
  BY DEF PReg!Cardinality, Cardinality

LEMMA RCardinalityBridge == \A T : RReg!Cardinality(T) = Cardinality(T)
  BY DEF RReg!Cardinality, Cardinality

THEOREM ParentUniqueSafety == Spec => []ParentUnique
  <1>1. Inv => ParentUnique
    <2> SUFFICES ASSUME Inv, NEW k \in Elements
                 PROVE  PReg!Cardinality({v \in Elements : <<k, v>> \in p_entries}) <= 1
      BY DEF ParentUnique, PReg!UniqueMapping
    <2> DEFINE S == {v \in Elements : <<k, v>> \in p_entries}
    <2>e. PReg!Cardinality(S) = Cardinality(S)
      BY PCardinalityBridge
    <2>1. CASE S = {}
      <3>1. Cardinality(S) = 0
        BY <2>1, FS_EmptySet
      <3> QED BY <3>1, <2>e
    <2>2. CASE S /= {}
      <3>1. PICK v0 \in S : TRUE
        BY <2>2
      <3>2. \A v \in S : v = v0
        BY <3>1 DEF Inv, InvPU, PUniqueOf
      <3>3. S = {v0}
        BY <3>1, <3>2
      <3>4. Cardinality(S) = 1
        BY <3>3, FS_Singleton
      <3> QED BY <3>4, <2>e
    <2> QED BY <2>1, <2>2
  <1> QED BY Safety, <1>1, PTL

THEOREM RankUniqueSafety == Spec => []RankUnique
  <1>1. Inv => RankUnique
    <2> SUFFICES ASSUME Inv, NEW k \in Elements
                 PROVE  RReg!Cardinality({v \in RankValues : <<k, v>> \in r_entries}) <= 1
      BY DEF RankUnique, RReg!UniqueMapping
    <2> DEFINE S == {v \in RankValues : <<k, v>> \in r_entries}
    <2>e. RReg!Cardinality(S) = Cardinality(S)
      BY RCardinalityBridge
    <2>1. CASE S = {}
      <3>1. Cardinality(S) = 0
        BY <2>1, FS_EmptySet
      <3> QED BY <3>1, <2>e
    <2>2. CASE S /= {}
      <3>1. PICK v0 \in S : TRUE
        BY <2>2
      <3>2. \A v \in S : v = v0
        BY <3>1 DEF Inv, InvRU, RUniqueOf
      <3>3. S = {v0}
        BY <3>1, <3>2
      <3>4. Cardinality(S) = 1
        BY <3>3, FS_Singleton
      <3> QED BY <3>4, <2>e
    <2> QED BY <2>1, <2>2
  <1> QED BY Safety, <1>1, PTL

(*-------------------------------------------------------------------------*)
(* The refinement: Init maps to EC!Init, every step maps to an EC step or  *)
(* an EC stutter.                                                          *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => EC!Init
  <1> SUFFICES ASSUME Init PROVE EC!Init
    OBVIOUS
  <1>e. p_entries = {} /\ r_entries = {} /\ b_allocated = 0
    BY DEF Init
  <1>p. MapParent = [e \in Elements |-> e]
    <2>1. MapParent = PView({})
      BY <1>e, MapParentIsPView
    <2> QED BY <2>1, PViewEmpty
  <1>r. MapRnk = [e \in Elements |-> 0]
    <2>1. MapRnk = RView({})
      BY <1>e, MapRnkIsRView
    <2> QED BY <2>1, RViewEmpty
  <1> QED BY <1>p, <1>r, <1>e DEF EC!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [EC!Next]_(EC!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [EC!Next]_(EC!vars)
    OBVIOUS
  <1>c. /\ p_entries \subseteq (Elements \X Elements)
        /\ r_entries \subseteq (Elements \X RankValues)
        /\ b_capacity = MaxOps
        /\ b_allocated \in 0..MaxOps
        /\ b_reserved = 0
        /\ b_pending = 0
    BY DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    <2>1. /\ p_entries' = p_entries
          /\ r_entries' = r_entries
          /\ b_allocated' = b_allocated
      BY <1>0 DEF vars
    <2>2. MapParent' = MapParent
      BY <2>1 DEF MapParent
    <2>3. MapRnk' = MapRnk
      BY <2>1 DEF MapRnk
    <2> QED BY <2>1, <2>2, <2>3 DEF EC!vars
  <1>1. CASE \E a \in Elements, b \in Elements : UnionStep(a, b)
    <2> SUFFICES ASSUME NEW a \in Elements, NEW b \in Elements, UnionStep(a, b)
                 PROVE  [EC!Next]_(EC!vars)
      BY <1>1
    <2> DEFINE ra == RepC(a)
    <2> DEFINE rb == RepC(b)
    <2>raE. ra \in Elements  BY RepCType
    <2>rbE. rb \in Elements  BY RepCType
    <2>rnkNat. MapRnk[ra] \in Nat /\ MapRnk[rb] \in Nat
      BY <2>raE, <2>rbE, MapRnkType, MaxOpsAss DEF RankValues
    <2>bud. b_allocated + b_reserved + b_pending + 1 <= b_capacity
      BY DEF UnionStep
    <2>ne. ra /= rb
      BY DEF UnionStep
    <2>opsP. b_allocated' = b_allocated + 1
      BY DEF UnionStep
    <2>ops2. b_allocated < MaxOps
      BY <2>bud, <1>c, MaxOpsAss
    <2>agA. EC!Rep(a) = ra  BY RepAgree
    <2>agB. EC!Rep(b) = rb  BY RepAgree
    <2>c1. CASE MapRnk[ra] < MapRnk[rb]
      <3>pp. p_entries' = Upsert(p_entries, ra, rb)
        BY <2>c1 DEF UnionStep
      <3>rp. r_entries' = r_entries
        BY <2>c1 DEF UnionStep
      <3>bp. MapParent' = [MapParent EXCEPT ![ra] = rb]
        <4>1. MapParent' = PView(p_entries')
          BY DEF MapParent, PView
        <4>2. PView(Upsert(p_entries, ra, rb)) = [PView(p_entries) EXCEPT ![ra] = rb]
          BY <2>raE, <2>rbE, PViewUpsert DEF Inv, InvPU
        <4> QED BY <4>1, <4>2, <3>pp, MapParentIsPView
      <3>br. MapRnk' = MapRnk
        BY <3>rp DEF MapRnk
      <3>u. EC!Union(a, b)
        BY <2>ops2, <2>ne, <2>c1, <2>agA, <2>agB, <3>bp, <3>br, <2>opsP,
           <2>rnkNat DEF EC!Union
      <3> QED BY <3>u DEF EC!Next
    <2>c2. CASE MapRnk[ra] > MapRnk[rb]
      <3>pp. p_entries' = Upsert(p_entries, rb, ra)
        BY <2>c2, <2>rnkNat DEF UnionStep
      <3>rp. r_entries' = r_entries
        BY <2>c2, <2>rnkNat DEF UnionStep
      <3>bp. MapParent' = [MapParent EXCEPT ![rb] = ra]
        <4>1. MapParent' = PView(p_entries')
          BY DEF MapParent, PView
        <4>2. PView(Upsert(p_entries, rb, ra)) = [PView(p_entries) EXCEPT ![rb] = ra]
          BY <2>raE, <2>rbE, PViewUpsert DEF Inv, InvPU
        <4> QED BY <4>1, <4>2, <3>pp, MapParentIsPView
      <3>br. MapRnk' = MapRnk
        BY <3>rp DEF MapRnk
      <3>u. EC!Union(a, b)
        BY <2>ops2, <2>ne, <2>c2, <2>agA, <2>agB, <3>bp, <3>br, <2>opsP,
           <2>rnkNat DEF EC!Union
      <3> QED BY <3>u DEF EC!Next
    <2>c3. CASE MapRnk[ra] = MapRnk[rb]
      <3>pp. p_entries' = Upsert(p_entries, rb, ra)
        BY <2>c3, <2>rnkNat DEF UnionStep
      <3>rp. r_entries' = Upsert(r_entries, ra, MapRnk[ra] + 1)
        BY <2>c3, <2>rnkNat DEF UnionStep
      <3>rv. MapRnk[ra] + 1 \in RankValues
        <4>1. MapRnk[ra] <= b_allocated
          BY <2>raE DEF Inv, RankOpsBoundC
        <4> QED BY <4>1, <2>ops2, <2>rnkNat, <1>c, MaxOpsAss DEF RankValues
      <3>bp. MapParent' = [MapParent EXCEPT ![rb] = ra]
        <4>1. MapParent' = PView(p_entries')
          BY DEF MapParent, PView
        <4>2. PView(Upsert(p_entries, rb, ra)) = [PView(p_entries) EXCEPT ![rb] = ra]
          BY <2>raE, <2>rbE, PViewUpsert DEF Inv, InvPU
        <4> QED BY <4>1, <4>2, <3>pp, MapParentIsPView
      <3>br. MapRnk' = [MapRnk EXCEPT ![ra] = MapRnk[ra] + 1]
        <4>1. MapRnk' = RView(r_entries')
          BY DEF MapRnk, RView
        <4>2. RView(Upsert(r_entries, ra, MapRnk[ra] + 1))
                = [RView(r_entries) EXCEPT ![ra] = MapRnk[ra] + 1]
          BY <2>raE, <3>rv, RViewUpsert DEF Inv, InvRU
        <4> QED BY <4>1, <4>2, <3>rp, MapRnkIsRView
      <3>u. EC!Union(a, b)
        BY <2>ops2, <2>ne, <2>c3, <2>agA, <2>agB, <3>bp, <3>br, <2>opsP,
           <2>rnkNat DEF EC!Union
      <3> QED BY <3>u DEF EC!Next
    <2> QED BY <2>c1, <2>c2, <2>c3, <2>rnkNat
  <1>2. CASE Idle
    <2>1. UNCHANGED vars
      BY <1>2 DEF Idle
    <2>2. b_allocated >= b_capacity
      BY <1>2 DEF Idle
    <2>3. b_allocated >= MaxOps
      BY <2>2, <1>c
    <2>4. /\ p_entries' = p_entries
          /\ r_entries' = r_entries
          /\ b_allocated' = b_allocated
      BY <2>1 DEF vars
    <2>5. MapParent' = MapParent
      BY <2>4 DEF MapParent
    <2>6. MapRnk' = MapRnk
      BY <2>4 DEF MapRnk
    <2>7. EC!Idle
      BY <2>3, <2>4, <2>5, <2>6 DEF EC!Idle, EC!vars
    <2> QED BY <2>7 DEF EC!Next
  <1> QED BY <1>0, <1>1, <1>2 DEF Next

(*-------------------------------------------------------------------------*)
(* The construction refines EquivalenceClass for the stated parameters.   *)
(*-------------------------------------------------------------------------*)
THEOREM Refinement == Spec => EC!Spec
  <1>1. Init => EC!Init
    BY InitRefines
  <1>2. Inv /\ [Next]_vars => [EC!Next]_(EC!vars)
    BY NextRefines
  <1>3. Spec => []Inv
    BY Safety
  <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec, EC!Spec

\* Restatement in the base module's own vocabulary.
THEOREM RefinementOriginal == Spec => ECRefinement
  BY Refinement DEF ECRefinement

====
