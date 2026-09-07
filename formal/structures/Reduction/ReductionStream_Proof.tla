---- MODULE ReductionStream_Proof ----
(***************************************************************************
  TLAPS proof for the ordered, exactly-once ReductionStream carrier.

  Discharges, unbounded and parametric in Src and Op, exactly the two
  invariants ReductionStream.cfg checks:

      TypeSafety             == Spec => []TypeInvariant
      ConsumedPrefixFoldSafety == Spec => []ConsumedPrefixFold

  ConsumedPrefixFold is the entry's obligation and it is inductive on its own:
  Consume combines the next element into the summary and advances past it in
  one step, which is exactly FoldPrefix's recursive clause. Splitting those
  effects makes the equality reachable-false.

  THE ONE PIECE OF MACHINERY. FoldPrefix is a recursive function over the
  finite interval 0..Len(Src), which TLA+ renders as a CHOOSE, so unfolding
  its definition says nothing about its values; the defining equation is
  recovered from the library's FiniteNatInductiveDef. This is the
  finite-interval form of the Nat-domain induction that Reduction_Proof uses
  for FoldCount.

  This module does not EXTEND SequenceTheorems, so Len(Src) \in Nat and the
  element typing are ASSUMEs here rather than derived from Src \in Seq(Nat)
  via LenProperties / ElementOfSeq. The library theorem's Def(_,_) is
  instantiated with the NAMED operator Comb, not a LAMBDA, and its two
  interval endpoints (NEW m, n \in Nat) are supplied as explicit facts.

  CONTRACTS. Four ASSUMEs, all typing. Reduction_Proof additionally needs
  Associative, IdentityLeft, and IdentityRight to
  state Reassociation and Aggregate over a SET. A stream fold is left-nested
  and consumed in order, so it needs none of them.
 ***************************************************************************)
EXTENDS ReductionStream, NaturalsInduction, TLAPS

ASSUME IdentityType == Identity \in Nat
ASSUME SrcLen == Len(Src) \in Nat
ASSUME SrcNat == \A i \in 1..Len(Src) : Src[i] \in Nat
ASSUME OpType == \A a, b \in Nat : Op(a, b) \in Nat

(*-------------------------------------------------------------------------*)
(* FoldPrefix satisfies its recursive definition.                          *)
(*-------------------------------------------------------------------------*)

\* The recursion's combine step, as a NAMED two-argument operator.
Comb(v, i) == Op(v, Src[i])

THEOREM FoldPrefixDefConclusion ==
    FiniteNatInductiveDefConclusion(FoldPrefix, Identity, Comb, 0, Len(Src))
  <1>1. FiniteNatInductiveDefHypothesis(FoldPrefix, Identity, Comb, 0, Len(Src))
    BY DEF FiniteNatInductiveDefHypothesis, FoldPrefix, Comb
  <1>2. 0 \in Nat          OBVIOUS
  <1>3. Len(Src) \in Nat   BY SrcLen
  <1> QED  BY <1>1, <1>2, <1>3, FiniteNatInductiveDef

LEMMA FoldPrefixDef ==
    \A i \in 0..Len(Src) :
        FoldPrefix[i] = IF i = 0 THEN Identity ELSE Op(FoldPrefix[i - 1], Src[i])
  BY FoldPrefixDefConclusion DEF FiniteNatInductiveDefConclusion, Comb

LEMMA FoldPrefixZero == FoldPrefix[0] = Identity
  <1>1. 0 \in 0..Len(Src)   BY SrcLen
  <1> QED  BY <1>1, FoldPrefixDef

LEMMA FoldPrefixStep ==
    ASSUME NEW k \in Nat, k + 1 \in 0..Len(Src)
    PROVE  FoldPrefix[k + 1] = Op(FoldPrefix[k], Src[k + 1])
  <1>1. k + 1 # 0                    OBVIOUS
  <1>2. FoldPrefix[k + 1] = IF k + 1 = 0
                              THEN Identity
                              ELSE Op(FoldPrefix[k + 1 - 1], Src[k + 1])
    BY FoldPrefixDef
  <1>3. k + 1 - 1 = k                OBVIOUS
  <1> QED  BY <1>1, <1>2, <1>3

(*-------------------------------------------------------------------------*)
(* The inductive invariant IS the two cfg invariants (the faithful-layer    *)
(* standard: no auxiliary content, no strengthening).                       *)
(*-------------------------------------------------------------------------*)
Inv == TypeInvariant /\ ConsumedPrefixFold

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>a. pos = 0 /\ result = Identity   BY DEF Init
  <1>1. TypeInvariant
    <2>1. pos \in 0..Len(Src)   BY <1>a, SrcLen
    <2>2. result \in Nat        BY <1>a, IdentityType
    <2> QED  BY <2>1, <2>2 DEF TypeInvariant
  <1>2. ConsumedPrefixFold        BY <1>a, FoldPrefixZero DEF ConsumedPrefixFold
  <1> QED  BY <1>1, <1>2 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, ConsumedPrefixFold
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE Next
    <2> USE <1>1 DEF Next, Consume
    <2>n. pos \in 0..Len(Src)          OBVIOUS
    <2>k. pos \in Nat                  BY <2>n, SrcLen
    <2>a. pos < Len(Src)               OBVIOUS
    <2>i. pos + 1 \in 1..Len(Src)      BY <2>a, <2>k, SrcLen
    <2>e. Src[pos + 1] \in Nat         BY <2>i, SrcNat
    <2>r. result \in Nat               OBVIOUS
    <2>b. result' = Op(result, Src[pos + 1])   OBVIOUS
    <2>c. pos' = pos + 1               OBVIOUS
    <2>1. TypeInvariant'
      <3>1. pos' \in 0..Len(Src)   BY <2>a, <2>c, <2>k, SrcLen
      <3>2. result' \in Nat        BY <2>b, <2>e, <2>r, OpType
      <3> QED  BY <3>1, <3>2
    <2>2. ConsumedPrefixFold'
      <3>1. pos + 1 \in 0..Len(Src)                            BY <2>a, <2>k, SrcLen
      <3>2. FoldPrefix[pos + 1] = Op(FoldPrefix[pos], Src[pos + 1])
        BY <2>k, <3>1, FoldPrefixStep
      <3>3. result = FoldPrefix[pos]                           OBVIOUS
      <3> QED  BY <2>b, <2>c, <3>2, <3>3
    <2> QED  BY <2>1, <2>2
  <1> QED  BY <1>0, <1>1

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'     BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

(*-------------------------------------------------------------------------*)
(* The two cfg invariants, as corollaries -- exactly the cfg set, no more.  *)
(*-------------------------------------------------------------------------*)
THEOREM TypeSafety == Spec => []TypeInvariant
  <1>1. Inv => TypeInvariant   BY DEF Inv
  <1> QED  BY Safety, <1>1, PTL

THEOREM ConsumedPrefixFoldSafety == Spec => []ConsumedPrefixFold
  <1>1. Inv => ConsumedPrefixFold   BY DEF Inv
  <1> QED  BY Safety, <1>1, PTL

====
