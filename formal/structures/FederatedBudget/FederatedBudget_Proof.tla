---- MODULE FederatedBudget_Proof ----
(* Safety proof for the master-capacity bound, each sub-pool capacity bound,
   and conservation of delegated capacity.

   CapSum folds sub_capacities over a fixed bijective enumeration of the finite
   set SubPoolNames. AllocateSubPool changes the master and one enumerated
   sub-pool by the same amount. CapSumUpdate proves the corresponding one-term
   delta by induction; the other actions leave the capacity vector unchanged. *)
EXTENDS FederatedBudget, Naturals, FiniteSets, FiniteSetTheorems,
        NaturalsInduction, TLAPS

ASSUME SubPoolNamesFinite == IsFiniteSet(SubPoolNames)
ASSUME MasterCapacityType == MasterCapacity \in Nat

\* ---- SubN, and the bijective enumeration SubEnum -------------------------
LEMMA SubNType == SubN \in Nat
  BY SubPoolNamesFinite, FS_CardinalityType DEF SubN

\* SubN and SubEnum depend only on the constant SubPoolNames.
LEMMA SubNConst == SubN' = SubN
  BY DEF SubN

LEMMA SubEnumConst == SubEnum' = SubEnum
  BY SubNConst DEF SubEnum

LEMMA SubEnumBij ==
  /\ SubEnum \in [1..SubN -> SubPoolNames]
  /\ \A n \in SubPoolNames : \E i \in 1..SubN : SubEnum[i] = n
  /\ \A i \in 1..SubN : \A j \in 1..SubN : SubEnum[i] = SubEnum[j] => i = j
  <1> DEFINE Q(seq) == \A n \in SubPoolNames : \E i \in 1..SubN : seq[i] = n
  \* The CHOOSE set is non-empty: a bijection 1..SubN -> SubPoolNames exists.
  <1>card. Cardinality(SubPoolNames) = SubN  BY DEF SubN
  <1>bij. ExistsBijection(1..SubN, SubPoolNames)
    BY SubPoolNamesFinite, FS_CardinalityType, <1>card
  <1>ex. \E seq \in [1..SubN -> SubPoolNames] : Q(seq)
    <2>1. PICK f \in Bijection(1..SubN, SubPoolNames) : TRUE
      BY <1>bij DEF ExistsBijection
    <2>2. f \in Surjection(1..SubN, SubPoolNames)  BY <2>1 DEF Bijection
    <2>3. f \in [1..SubN -> SubPoolNames] /\ Q(f)  BY <2>2 DEF Surjection
    <2> QED  BY <2>3
  <1>1. SubEnum \in [1..SubN -> SubPoolNames] /\ Q(SubEnum)
    BY <1>ex DEF SubEnum
  \* Injective: a surjection between equal-cardinality finite sets is injective.
  <1>fin. IsFiniteSet(1..SubN)  BY SubNType, FS_Interval
  <1>surj. SubEnum \in Surjection(1..SubN, SubPoolNames)
    BY <1>1 DEF Surjection
  <1>cc. Cardinality(1..SubN) = Cardinality(SubPoolNames)
    <2>1. Cardinality(1..SubN) = SubN  BY SubNType, FS_Interval
    <2> QED  BY <2>1, <1>card
  <1>inj. SubEnum \in Injection(1..SubN, SubPoolNames)
    BY <1>surj, <1>fin, <1>cc, FS_Surjection
  <1>2. \A i \in 1..SubN : \A j \in 1..SubN : SubEnum[i] = SubEnum[j] => i = j
    BY <1>inj DEF Injection, IsInjective
  <1> QED  BY <1>1, <1>2

\* ---- CapSum recursion equation (current state and primed state) -----------
THEOREM CapSumConcl ==
  FiniteNatInductiveDefConclusion(CapSum, 0, LAMBDA p, i : p + sub_capacities[SubEnum[i]], 0, SubN)
  <1>1. FiniteNatInductiveDefHypothesis(CapSum, 0, LAMBDA p, i : p + sub_capacities[SubEnum[i]], 0, SubN)
    BY DEF FiniteNatInductiveDefHypothesis, CapSum
  <1> QED  BY <1>1, SubNType, FiniteNatInductiveDef

LEMMA CapSumRec ==
  CapSum = [i \in 0..SubN |-> IF i = 0 THEN 0 ELSE CapSum[i - 1] + sub_capacities[SubEnum[i]]]
  BY CapSumConcl DEF FiniteNatInductiveDefConclusion

THEOREM CapSumConclPrime ==
  FiniteNatInductiveDefConclusion(CapSum', 0, LAMBDA p, i : p + sub_capacities'[SubEnum[i]], 0, SubN)
  <1>1. FiniteNatInductiveDefHypothesis(CapSum', 0, LAMBDA p, i : p + sub_capacities'[SubEnum[i]], 0, SubN)
    BY SubNConst, SubEnumConst DEF FiniteNatInductiveDefHypothesis, CapSum
  <1> QED  BY <1>1, SubNType, FiniteNatInductiveDef

LEMMA CapSumRecPrime ==
  CapSum' = [i \in 0..SubN |-> IF i = 0 THEN 0 ELSE CapSum'[i - 1] + sub_capacities'[SubEnum[i]]]
  BY CapSumConclPrime DEF FiniteNatInductiveDefConclusion

\* ---- Fold facts: typing, one-element delta, stability ---------------------
\* All three are stated generically over fold functions G, H given by their
\* recursion equations, so they apply to CapSum (current) and CapSum' (primed).

LEMMA FoldType ==
  ASSUME NEW g \in [SubPoolNames -> Nat], NEW G,
         G = [i \in 0..SubN |-> IF i = 0 THEN 0 ELSE G[i - 1] + g[SubEnum[i]]]
  PROVE  \A i \in 0..SubN : G[i] \in Nat
  <1> USE SubNType
  <1> DEFINE P(k) == k \in 0..SubN => G[k] \in Nat
  <1>1. P(0)
    OBVIOUS
  <1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
    <2> SUFFICES ASSUME k + 1 \in 0..SubN PROVE G[k + 1] \in Nat  OBVIOUS
    <2>k. k \in 0..SubN  OBVIOUS
    <2>e. SubEnum[k + 1] \in SubPoolNames  BY SubEnumBij
    <2>1. G[k + 1] = G[k] + g[SubEnum[k + 1]]  BY <2>k
    <2>2. G[k] \in Nat  BY <2>k, P(k)
    <2>3. g[SubEnum[k + 1]] \in Nat  BY <2>e
    <2> QED  BY <2>1, <2>2, <2>3
  <1>3. \A k \in Nat : P(k)  BY <1>1, <1>2, NatInduction
  <1> QED  BY <1>3

\* Appending an enumeration position that is not nm cannot change whether nm
\* has appeared.  Keep this finite-interval fact out of FoldDelta's large
\* arithmetic context so its use is a direct theorem match.
LEMMA SeenAppendNonmatch ==
  ASSUME NEW k \in Nat, NEW nm,
         SubEnum[k + 1] # nm
  PROVE  (\E j \in 1..(k + 1) : SubEnum[j] = nm)
          <=> (\E j \in 1..k : SubEnum[j] = nm)
  <1>forward. (\E j \in 1..(k + 1) : SubEnum[j] = nm)
               => (\E j \in 1..k : SubEnum[j] = nm)
    <2> SUFFICES ASSUME \E j \in 1..(k + 1) : SubEnum[j] = nm
                 PROVE  \E j \in 1..k : SubEnum[j] = nm
      OBVIOUS
    <2> PICK j \in 1..(k + 1) : SubEnum[j] = nm  OBVIOUS
    <2>neq. j # k + 1  OBVIOUS
    <2>old. j \in 1..k  BY <2>neq
    <2> QED  BY <2>old
  <1>back. (\E j \in 1..k : SubEnum[j] = nm)
              => (\E j \in 1..(k + 1) : SubEnum[j] = nm)
    <2> SUFFICES ASSUME \E j \in 1..k : SubEnum[j] = nm
                 PROVE  \E j \in 1..(k + 1) : SubEnum[j] = nm
      OBVIOUS
    <2> PICK j \in 1..k : SubEnum[j] = nm  OBVIOUS
    <2>new. j \in 1..(k + 1)  OBVIOUS
    <2> QED  BY <2>new
  <1> QED  BY <1>forward, <1>back

\* Arithmetic bridge used by the unchanged-enumeration branch of FoldDelta.
\* Its clean context avoids asking the backend to normalize mixed Nat/Int
\* addition while the full recursive-fold hypotheses are in scope.
LEMMA NatIntDeltaReassociate ==
  ASSUME NEW x \in Nat, NEW y \in Nat, NEW d \in Int
  PROVE  (x + d) + y = (x + y) + d
  OBVIOUS

LEMMA NatIntDeltaRightReassociate ==
  ASSUME NEW x \in Nat, NEW y \in Nat, NEW d \in Int
  PROVE  x + (y + d) = (x + y) + d
  OBVIOUS

LEMMA FoldDelta ==
  ASSUME NEW g \in [SubPoolNames -> Nat], NEW h \in [SubPoolNames -> Nat],
         NEW nm \in SubPoolNames, NEW d \in Int,
         h = [g EXCEPT ![nm] = g[nm] + d],
         NEW G, NEW H,
         G = [i \in 0..SubN |-> IF i = 0 THEN 0 ELSE G[i - 1] + g[SubEnum[i]]],
         H = [i \in 0..SubN |-> IF i = 0 THEN 0 ELSE H[i - 1] + h[SubEnum[i]]]
  PROVE  H[SubN] = G[SubN] + d
  <1> USE SubNType
  <1>gN. \A i \in 0..SubN : G[i] \in Nat  BY FoldType
  <1> DEFINE Seen(k) == \E j \in 1..k : SubEnum[j] = nm
  <1> DEFINE P(k) == k \in 0..SubN =>
                       H[k] = G[k] + (IF Seen(k) THEN d ELSE 0)
  <1>1. P(0)
    <2> SUFFICES ASSUME 0 \in 0..SubN PROVE H[0] = G[0] + (IF Seen(0) THEN d ELSE 0)  OBVIOUS
    <2>1. H[0] = 0 /\ G[0] = 0  OBVIOUS
    <2>2. ~ Seen(0)  OBVIOUS
    <2> QED  BY <2>1, <2>2
  <1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
    <2> SUFFICES ASSUME k + 1 \in 0..SubN
                 PROVE  H[k + 1] = G[k + 1] + (IF Seen(k + 1) THEN d ELSE 0)
      OBVIOUS
    <2>k. k \in 0..SubN  OBVIOUS
    <2>e. SubEnum[k + 1] \in SubPoolNames  BY SubEnumBij
    <2>gk. G[k] \in Nat  BY <2>k, <1>gN
    <2>gN1. g[SubEnum[k + 1]] \in Nat  BY <2>e
    <2>Geq. G[k + 1] = G[k] + g[SubEnum[k + 1]]  BY <2>k
    <2>Heq. H[k + 1] = H[k] + h[SubEnum[k + 1]]  BY <2>k
    <2>hval. h[SubEnum[k + 1]] = IF SubEnum[k + 1] = nm THEN g[nm] + d ELSE g[SubEnum[k + 1]]
      BY <2>e
    <2>ih. H[k] = G[k] + (IF Seen(k) THEN d ELSE 0)  BY <2>k, P(k)
    <2>A. CASE SubEnum[k + 1] = nm
      \* The changed name sits at k+1; by injectivity it is at no earlier index.
      <3>notseen. ~ Seen(k)
        <4> SUFFICES ASSUME NEW j \in 1..k, SubEnum[j] = nm PROVE FALSE  OBVIOUS
        <4>1. j \in 1..SubN /\ (k + 1) \in 1..SubN  OBVIOUS
        <4>2. SubEnum[j] = SubEnum[k + 1]  BY <2>A
        <4>3. j = k + 1  BY <4>1, <4>2, SubEnumBij
        <4> QED  BY <4>3
      <3>seen1. Seen(k + 1)  BY <2>A
      <3>hv. h[SubEnum[k + 1]] = g[nm] + d  BY <2>hval, <2>A
      <3>gv. g[SubEnum[k + 1]] = g[nm]  BY <2>A
      <3>ih0. H[k] = G[k]  BY <2>ih, <3>notseen, <2>gk
      <3>1. H[k + 1] = G[k] + (g[nm] + d)  BY <2>Heq, <3>hv, <3>ih0
      <3>2. G[k + 1] = G[k] + g[nm]  BY <2>Geq, <3>gv
      <3>arith. G[k] + (g[nm] + d) = (G[k] + g[nm]) + d
        BY <2>gk, <2>gN1, <3>gv, NatIntDeltaRightReassociate
      <3> QED  BY <3>1, <3>2, <3>seen1, <3>arith
    <2>B. CASE SubEnum[k + 1] # nm
      <3>hv. h[SubEnum[k + 1]] = g[SubEnum[k + 1]]  BY <2>hval, <2>B
      <3>seeneq. Seen(k + 1) <=> Seen(k)
        BY <2>B, SeenAppendNonmatch DEF Seen
      <3>1. H[k + 1] = G[k] + (IF Seen(k) THEN d ELSE 0) + g[SubEnum[k + 1]]
        BY <2>Heq, <3>hv, <2>ih
      <3>iteeq. (IF Seen(k + 1) THEN d ELSE 0) = (IF Seen(k) THEN d ELSE 0)
        BY <3>seeneq
      <3>dint. (IF Seen(k) THEN d ELSE 0) \in Int  OBVIOUS
      <3>arith. (G[k] + (IF Seen(k) THEN d ELSE 0)) + g[SubEnum[k + 1]]
                 = (G[k] + g[SubEnum[k + 1]]) + (IF Seen(k) THEN d ELSE 0)
        BY <2>gk, <2>gN1, <3>dint, NatIntDeltaReassociate
      <3> QED  BY <3>1, <2>Geq, <3>iteeq, <3>arith
    <2> QED  BY <2>A, <2>B
  <1>3. \A k \in Nat : P(k)  BY <1>1, <1>2, NatInduction
  <1>4. P(SubN)  BY <1>3
  <1>seen. Seen(SubN)  BY SubEnumBij
  <1> QED  BY <1>4, <1>seen

\* State-level stability proof for unchanged capacities.  Prove the recursive
\* equality once in a clean context and cite this narrow bridge at each
\* unchanged-capacity site in NextInv.
LEMMA CapSumStable ==
  ASSUME sub_capacities \in [SubPoolNames -> Nat],
         sub_capacities' = sub_capacities
  PROVE  CapSum'[SubN] = CapSum[SubN]
  <1>rec. CapSum = [i \in 0..SubN |-> IF i = 0 THEN 0 ELSE CapSum[i - 1] + sub_capacities[SubEnum[i]]]
    BY CapSumRec
  <1>recP. CapSum' = [i \in 0..SubN |-> IF i = 0 THEN 0 ELSE CapSum'[i - 1] + sub_capacities[SubEnum[i]]]
    BY CapSumRecPrime
  <1> DEFINE P(k) == k \in 0..SubN => CapSum'[k] = CapSum[k]
  <1>1. P(0)  BY <1>rec, <1>recP, SubNType
  <1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
    <2> SUFFICES ASSUME k + 1 \in 0..SubN PROVE CapSum'[k + 1] = CapSum[k + 1]
      OBVIOUS
    <2>k. k \in 0..SubN  BY SubNType
    <2>p. CapSum'[k + 1] = CapSum'[k] + sub_capacities[SubEnum[k + 1]]
      BY <2>k, <1>recP
    <2>u. CapSum[k + 1] = CapSum[k] + sub_capacities[SubEnum[k + 1]]
      BY <2>k, <1>rec
    <2>ih. CapSum'[k] = CapSum[k]  BY <2>k, P(k)
    <2> QED  BY <2>p, <2>u, <2>ih
  <1>3. \A k \in Nat : P(k)  BY <1>1, <1>2, NatInduction
  <1> QED  BY <1>3, SubNType

\* ---- The inductive invariant ----------------------------------------------
Inv == TypeInvariant /\ MasterCapacityBound /\ SubPoolCapacityBound /\ CapacityConservation

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1> USE DEF Init
  <1>1. TypeInvariant
    BY DEF TypeInvariant
  <1>2. MasterCapacityBound
    BY MasterCapacityType DEF MasterCapacityBound
  <1>3. SubPoolCapacityBound
    BY DEF SubPoolCapacityBound
  <1>4. CapacityConservation
    \* sub_capacities = [n |-> 0], so every CapSum term is 0; CapSum[SubN] = 0.
    <2>z. sub_capacities = [n \in SubPoolNames |-> 0]  BY DEF Init
    <2>zero. \A i \in 0..SubN : CapSum[i] = 0
      <3> DEFINE P(k) == k \in 0..SubN => CapSum[k] = 0
      <3>1. P(0)
        BY CapSumRec, SubNType
      <3>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
        <4> SUFFICES ASSUME k + 1 \in 0..SubN PROVE CapSum[k + 1] = 0  OBVIOUS
        <4>k. k \in 0..SubN  BY SubNType
        <4>e. SubEnum[k + 1] \in SubPoolNames  BY SubEnumBij
        <4>1. CapSum[k + 1] = CapSum[k] + sub_capacities[SubEnum[k + 1]]
          BY CapSumRec, SubNType
        <4>2. sub_capacities[SubEnum[k + 1]] = 0  BY <2>z, <4>e
        <4>3. CapSum[k] = 0  BY <4>k, P(k)
        <4> QED  BY <4>1, <4>2, <4>3
      <3>3. \A k \in Nat : P(k)  BY <3>1, <3>2, NatInduction
      <3> QED  BY <3>3, SubNType
    <2>1. CapSum[SubN] = 0  BY <2>zero, SubNType
    <2> QED  BY <2>1 DEF CapacityConservation, Init
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, MasterCapacityBound, SubPoolCapacityBound
  <1> USE SubNType
  <1>rec.  CapSum  = [i \in 0..SubN |-> IF i = 0 THEN 0 ELSE CapSum[i - 1]  + sub_capacities[SubEnum[i]]]
    BY CapSumRec
  <1>recP. CapSum' = [i \in 0..SubN |-> IF i = 0 THEN 0 ELSE CapSum'[i - 1] + sub_capacities'[SubEnum[i]]]
    BY CapSumRecPrime
  <1>con. master_allocated = CapSum[SubN]  BY DEF CapacityConservation
  <1>0. CASE UNCHANGED vars
    <2> USE <1>0 DEF vars
    <2>1. TypeInvariant'  BY DEF TypeInvariant
    <2>2. MasterCapacityBound'  BY DEF MasterCapacityBound
    <2>3. SubPoolCapacityBound'  BY DEF SubPoolCapacityBound
    <2>4. CapacityConservation'
      <3>cap. sub_capacities \in [SubPoolNames -> Nat]  BY DEF TypeInvariant
      <3>same. sub_capacities' = sub_capacities  OBVIOUS
      <3>1. CapSum'[SubN] = CapSum[SubN]  BY <3>cap, <3>same, CapSumStable
      <3> QED  BY <3>1, <1>con DEF CapacityConservation
    <2> QED  BY <2>1, <2>2, <2>3, <2>4 DEF Inv
  <1>1. CASE \E name \in SubPoolNames, a \in 1..MasterCapacity : AllocateSubPool(name, a)
    <2> SUFFICES ASSUME NEW name \in SubPoolNames, NEW a \in 1..MasterCapacity,
                        AllocateSubPool(name, a)
                 PROVE  Inv'
      BY <1>1
    <2> USE DEF AllocateSubPool
    <2>cap. sub_capacities \in [SubPoolNames -> Nat]  BY DEF TypeInvariant
    <2>aN. a \in Nat /\ a >= 1  BY MasterCapacityType
    <2>A. CASE master_allocated + a <= MasterCapacity
      <3>mp. master_allocated' = master_allocated + a  BY <2>A
      <3>sp. sub_capacities' = [sub_capacities EXCEPT ![name] = sub_capacities[name] + a]  BY <2>A
      <3>up. sub_allocated' = sub_allocated  BY <2>A
      <3>capP. sub_capacities' \in [SubPoolNames -> Nat]
        BY <3>sp, <2>cap, <2>aN
      <3>1. TypeInvariant'
        BY <3>mp, <3>sp, <3>up, <3>capP, <2>cap, <2>aN, MasterCapacityType DEF TypeInvariant
      <3>2. MasterCapacityBound'
        BY <3>mp, <2>A DEF MasterCapacityBound
      <3>3. SubPoolCapacityBound'
        <4> SUFFICES ASSUME NEW n \in SubPoolNames PROVE sub_allocated'[n] <= sub_capacities'[n]
          BY DEF SubPoolCapacityBound
        <4>old. sub_allocated[n] <= sub_capacities[n]  BY DEF SubPoolCapacityBound
        <4>spv. sub_capacities'[n] = IF n = name THEN sub_capacities[name] + a ELSE sub_capacities[n]
          BY <3>sp, <2>cap
        <4>aN2. sub_capacities[n] \in Nat /\ sub_capacities[name] \in Nat  BY <2>cap
        <4> QED  BY <4>old, <4>spv, <3>up, <4>aN2, <2>aN
      <3>4. CapacityConservation'
        <4>delta. CapSum'[SubN] = CapSum[SubN] + a
          BY <2>cap, <3>capP, <3>sp, <2>aN, <1>rec, <1>recP, FoldDelta
        <4> QED  BY <4>delta, <3>mp, <1>con DEF CapacityConservation
      <3> QED  BY <3>1, <3>2, <3>3, <3>4 DEF Inv
    <2>B. CASE ~(master_allocated + a <= MasterCapacity)
      <3> USE <2>B
      <3>unch. UNCHANGED vars  BY DEF vars
      <3>1. TypeInvariant'  BY <3>unch DEF TypeInvariant, vars
      <3>2. MasterCapacityBound'  BY <3>unch DEF MasterCapacityBound, vars
      <3>3. SubPoolCapacityBound'  BY <3>unch DEF SubPoolCapacityBound, vars
      <3>4. CapacityConservation'
        <4>cap2. sub_capacities \in [SubPoolNames -> Nat]  BY DEF TypeInvariant
        <4>same. sub_capacities' = sub_capacities  BY <3>unch DEF vars
        <4>1. CapSum'[SubN] = CapSum[SubN]  BY <4>cap2, <4>same, CapSumStable
        <4>msame. master_allocated' = master_allocated  BY <3>unch DEF vars
        <4> QED  BY <4>1, <4>msame, <1>con DEF CapacityConservation
      <3> QED  BY <3>1, <3>2, <3>3, <3>4 DEF Inv
    <2> QED  BY <2>A, <2>B
  <1>2. CASE \E name \in SubPoolNames, a \in 1..MasterCapacity : AllocateFromSubPool(name, a)
    <2> SUFFICES ASSUME NEW name \in SubPoolNames, NEW a \in 1..MasterCapacity,
                        AllocateFromSubPool(name, a)
                 PROVE  Inv'
      BY <1>2
    <2> USE DEF AllocateFromSubPool
    <2>cap. sub_capacities \in [SubPoolNames -> Nat]  BY DEF TypeInvariant
    <2>mc. master_allocated' = master_allocated /\ sub_capacities' = sub_capacities
      BY DEF vars
    <2>A. CASE sub_allocated[name] + a <= sub_capacities[name]
      <3>up. sub_allocated' = [sub_allocated EXCEPT ![name] = sub_allocated[name] + a]  BY <2>A
      <3>aN. a \in Nat /\ a >= 1  BY MasterCapacityType
      <3>1. TypeInvariant'
        <4>uaN. sub_allocated' \in [SubPoolNames -> Nat]
          BY <3>up, <3>aN DEF TypeInvariant
        <4> QED  BY <4>uaN, <2>mc DEF TypeInvariant
      <3>2. MasterCapacityBound'  BY <2>mc DEF MasterCapacityBound
      <3>3. SubPoolCapacityBound'
        <4> SUFFICES ASSUME NEW n \in SubPoolNames PROVE sub_allocated'[n] <= sub_capacities'[n]
          BY DEF SubPoolCapacityBound
        <4>old. sub_allocated[n] <= sub_capacities[n]  BY DEF SubPoolCapacityBound
        <4>uav. sub_allocated'[n] = IF n = name THEN sub_allocated[name] + a ELSE sub_allocated[n]
          BY <3>up DEF TypeInvariant
        <4> QED  BY <4>old, <4>uav, <2>mc, <2>A
      <3>4. CapacityConservation'
        <4>1. CapSum'[SubN] = CapSum[SubN]  BY <2>cap, <2>mc, CapSumStable
        <4> QED  BY <4>1, <2>mc, <1>con DEF CapacityConservation
      <3> QED  BY <3>1, <3>2, <3>3, <3>4 DEF Inv
    <2>B. CASE ~(sub_allocated[name] + a <= sub_capacities[name])
      <3> USE <2>B
      <3>unch. UNCHANGED vars  BY DEF vars
      <3>1. TypeInvariant'  BY <3>unch DEF TypeInvariant, vars
      <3>2. MasterCapacityBound'  BY <3>unch DEF MasterCapacityBound, vars
      <3>3. SubPoolCapacityBound'  BY <3>unch DEF SubPoolCapacityBound, vars
      <3>4. CapacityConservation'
        <4>same. sub_capacities' = sub_capacities  BY <3>unch DEF vars
        <4>1. CapSum'[SubN] = CapSum[SubN]  BY <2>cap, <4>same, CapSumStable
        <4>msame. master_allocated' = master_allocated  BY <3>unch DEF vars
        <4> QED  BY <4>1, <4>msame, <1>con DEF CapacityConservation
      <3> QED  BY <3>1, <3>2, <3>3, <3>4 DEF Inv
    <2> QED  BY <2>A, <2>B
  <1>3. CASE \E name \in SubPoolNames, a \in 1..MasterCapacity : ReleaseFromSubPool(name, a)
    <2> SUFFICES ASSUME NEW name \in SubPoolNames, NEW a \in 1..MasterCapacity,
                        ReleaseFromSubPool(name, a)
                 PROVE  Inv'
      BY <1>3
    <2> USE DEF ReleaseFromSubPool
    <2>cap. sub_capacities \in [SubPoolNames -> Nat]  BY DEF TypeInvariant
    <2>g. a <= sub_allocated[name]  OBVIOUS
    <2>up. sub_allocated' = [sub_allocated EXCEPT ![name] = sub_allocated[name] - a]  OBVIOUS
    <2>mc. master_allocated' = master_allocated /\ sub_capacities' = sub_capacities  BY DEF vars
    <2>aN. a \in Nat  BY MasterCapacityType
    <2>1. TypeInvariant'
      <3>aaN. sub_allocated[name] \in Nat  BY DEF TypeInvariant
      <3>uaN. sub_allocated' \in [SubPoolNames -> Nat]
        BY <2>up, <2>g, <3>aaN, <2>aN DEF TypeInvariant
      <3> QED  BY <3>uaN, <2>mc DEF TypeInvariant
    <2>2. MasterCapacityBound'  BY <2>mc DEF MasterCapacityBound
    <2>3. SubPoolCapacityBound'
      <3> SUFFICES ASSUME NEW n \in SubPoolNames PROVE sub_allocated'[n] <= sub_capacities'[n]
        BY DEF SubPoolCapacityBound
      <3>old. sub_allocated[n] <= sub_capacities[n]  BY DEF SubPoolCapacityBound
      <3>aaN. sub_allocated[name] \in Nat  BY DEF TypeInvariant
      <3>uav. sub_allocated'[n] = IF n = name THEN sub_allocated[name] - a ELSE sub_allocated[n]
        BY <2>up DEF TypeInvariant
      <3> QED  BY <3>old, <3>uav, <2>mc, <2>g, <2>aN, <3>aaN
    <2>4. CapacityConservation'
      <3>1. CapSum'[SubN] = CapSum[SubN]  BY <2>cap, <2>mc, CapSumStable
      <3> QED  BY <3>1, <2>mc, <1>con DEF CapacityConservation
    <2> QED  BY <2>1, <2>2, <2>3, <2>4 DEF Inv
  <1>X. CASE Next
    BY <1>X, <1>1, <1>2, <1>3 DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                  BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'   BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant                   BY Safety, PTL DEF Inv
THEOREM MasterCapacityBoundSafety == Spec => []MasterCapacityBound       BY Safety, PTL DEF Inv
THEOREM SubPoolCapacityBoundSafety == Spec => []SubPoolCapacityBound             BY Safety, PTL DEF Inv
THEOREM CapacityConservationSafety == Spec => []CapacityConservation     BY Safety, PTL DEF Inv
====
