---- MODULE ReductionStreamFromAuditSink_Proof ----
(***************************************************************************
  TLAPS proof of the ReductionStream-from-AuditSink refinement.

  Discharges, unbounded and parametric in Src and Op:

      Refinement == Spec => RS!Spec

  The proof is organized around one inductive fact:

      last_hash = RS!FoldPrefix[Len(log)]

  AuditSink's chain carry is the left fold of the consumed prefix. The
  step is immediate from Record's body -- the new carry is Op(old carry,
  element), and that is the recursive clause of FoldPrefix. The argument uses
  the component transition definition directly; the separately model-checked
  ChainSafety conjunction is not a premise of this TLAPS refinement proof.

  RS!FoldPrefix is a
  recursive function over the finite interval 0..Len(Src), which TLA+ renders
  as a CHOOSE; unfolding the definition therefore proves nothing about its
  values, and the defining equation has to be recovered from the library.
  Reduction_Proof does this for its Nat-domain FoldCount
  (NatInductiveDef); this proof uses the finite-interval twin,
  FiniteNatInductiveDef. Same idiom, same three consequences
  (Def / Zero / Step).

  Two constraints on how the proof is written:

  1. This module does not EXTEND SequenceTheorems, because doing so in a
     module that uses NaturalsInduction makes tlapm rename NaturalsInduction's
     definitions with _1 suffixes. That desynchronizes its theorems from the
     definitions their own statements are written in, and
     FiniteNatInductiveDef then fails to apply even to a verbatim restatement
     of itself, as does NatInductiveDef. The two typing facts about Src are
     therefore ASSUMEs here rather than derived from Src \in Seq(Nat) via
     LenProperties / ElementOfSeq.
  2. The library theorem's Def(_,_) is instantiated with the NAMED operator
     Comb rather than a LAMBDA, and its two interval endpoints (NEW m, n \in
     Nat) are supplied as explicit facts.

  Contracts: four ASSUMEs -- typing, plus Identity = 0. The base
  Reduction_Proof carries six (ItemsFinite, IdentityType, OpType,
  Associative, IdentityLeft, IdentityRight):

    IdentityZero -- Identity = 0, matching AuditSink's initialization of
                    last_hash to 0. Stated explicitly as a claim condition.
    SrcLen       -- Len(Src) \in Nat: the stream is finite. Typing.
    SrcNat       -- its elements are values. Typing.
    OpClosed     -- typing of the combine.

  Associativity is absent. The base Reduction model needs Associative /
  IdentityLeft / IdentityRight to state Reassociation and Aggregate over a
  SET. A stream fold is left-nested and consumed in order, so it needs none
  of them, and neither does a hash chain, which is what lets a chain serve as
  the fold. The reduction costs the entry strictly fewer contracts than it
  already had.
 ***************************************************************************)
EXTENDS ReductionStreamFromAuditSink, NaturalsInduction, TLAPS

ASSUME IdentityZero == Identity = 0
ASSUME SrcLen == Len(Src) \in Nat
ASSUME SrcNat == \A i \in 1..Len(Src) : Src[i] \in Nat
ASSUME OpClosed == \A a, b \in Nat : Op(a, b) \in Nat

(*-------------------------------------------------------------------------*)
(* FoldPrefix satisfies its recursive definition.                          *)
(*-------------------------------------------------------------------------*)

\* The recursion's combine step, as a NAMED two-argument operator rather than
\* a LAMBDA (note 2 above).
Comb(v, i) == Op(v, Src[i])

THEOREM FoldPrefixDefConclusion ==
    FiniteNatInductiveDefConclusion(RS!FoldPrefix, Identity, Comb, 0, Len(Src))
  <1>1. FiniteNatInductiveDefHypothesis(RS!FoldPrefix, Identity, Comb, 0, Len(Src))
    BY DEF FiniteNatInductiveDefHypothesis, RS!FoldPrefix, Comb
  <1>2. 0 \in Nat          OBVIOUS
  <1>3. Len(Src) \in Nat   BY SrcLen
  <1> QED  BY <1>1, <1>2, <1>3, FiniteNatInductiveDef

LEMMA FoldPrefixDef ==
    \A i \in 0..Len(Src) :
        RS!FoldPrefix[i] = IF i = 0 THEN Identity
                                    ELSE Op(RS!FoldPrefix[i - 1], Src[i])
  BY FoldPrefixDefConclusion DEF FiniteNatInductiveDefConclusion, Comb

LEMMA FoldPrefixZero == RS!FoldPrefix[0] = Identity
  <1>1. 0 \in 0..Len(Src)   BY SrcLen
  <1> QED  BY <1>1, FoldPrefixDef

LEMMA FoldPrefixStep ==
    ASSUME NEW k \in Nat, k + 1 \in 0..Len(Src)
    PROVE  RS!FoldPrefix[k + 1] = Op(RS!FoldPrefix[k], Src[k + 1])
  <1>1. k + 1 # 0                    OBVIOUS
  <1>2. RS!FoldPrefix[k + 1] = IF k + 1 = 0
                                 THEN Identity
                                 ELSE Op(RS!FoldPrefix[k + 1 - 1], Src[k + 1])
    BY FoldPrefixDef
  <1>3. k + 1 - 1 = k                OBVIOUS
  <1> QED  BY <1>1, <1>2, <1>3

(*-------------------------------------------------------------------------*)
(* The inductive invariant.                                                *)
(*-------------------------------------------------------------------------*)
TypeOK ==
    /\ last_hash \in Nat
    /\ Len(log) \in 0..Len(Src)

\* The one fact: the chain carry is the fold of the consumed prefix.
FoldOK == last_hash = RS!FoldPrefix[Len(log)]

Inv == TypeOK /\ FoldOK

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>a. log = <<>> /\ last_hash = 0   BY DEF Init, ASink!Init
  <1>1. Len(log) = 0                  BY <1>a
  <1>2. TypeOK                        BY <1>a, <1>1, SrcLen DEF TypeOK
  <1>3. RS!FoldPrefix[0] = Identity   BY FoldPrefixZero
  <1>4. FoldOK
    BY <1>a, <1>1, <1>3, IdentityZero DEF FoldOK
  <1> QED  BY <1>2, <1>4 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeOK, FoldOK
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE Next
    <2> USE <1>1 DEF Next, CConsume, ASink!Record
    <2>n. Len(log) \in 0..Len(Src)              OBVIOUS
    <2>k. Len(log) \in Nat                      BY <2>n, SrcLen
    <2>a. Len(log) < Len(Src)                   OBVIOUS
    <2>i. Len(log) + 1 \in 1..Len(Src)          BY <2>a, <2>k, SrcLen
    <2>e. Src[Len(log) + 1] \in Nat             BY <2>i, SrcNat
    <2>b. last_hash' = Op(last_hash, Src[Len(log) + 1])   OBVIOUS
    <2>c. Len(log') = Len(log) + 1
      <3>1. log' = Append(log, [operation |-> Src[Len(log) + 1],
                               prev_hash |-> last_hash,
                               hash      |-> Op(last_hash, Src[Len(log) + 1])])
        OBVIOUS
      <3> QED  BY <3>1
    <2>1. TypeOK'
      <3>1. last_hash' \in Nat          BY <2>b, <2>e, OpClosed
      <3>2. Len(log') \in 0..Len(Src)   BY <2>a, <2>c, <2>k, SrcLen
      <3> QED  BY <3>1, <3>2
    <2>2. FoldOK'
      <3>1. Len(log) + 1 \in 0..Len(Src)        BY <2>a, <2>k, SrcLen
      <3>3. RS!FoldPrefix[Len(log) + 1]
              = Op(RS!FoldPrefix[Len(log)], Src[Len(log) + 1])
        BY <2>k, <3>1, FoldPrefixStep
      <3>4. last_hash = RS!FoldPrefix[Len(log)]  OBVIOUS
      <3> QED  BY <2>b, <2>c, <3>3, <3>4
    <2> QED  BY <2>1, <2>2
  <1> QED  BY <1>0, <1>1

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'     BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

(*-------------------------------------------------------------------------*)
(* The refinement.                                                         *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => RS!Init
  <1> SUFFICES ASSUME Init PROVE RS!Init  OBVIOUS
  <1>a. log = <<>> /\ last_hash = 0   BY DEF Init, ASink!Init
  <1>1. PosView = 0                   BY <1>a DEF PosView
  <1>2. ResultView = Identity         BY <1>a, IdentityZero DEF ResultView
  <1> QED  BY <1>1, <1>2 DEF RS!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [RS!Next]_(RS!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [RS!Next]_(RS!vars)  OBVIOUS
  <1>0. CASE UNCHANGED vars
    <2>1. log' = log /\ last_hash' = last_hash   BY <1>0 DEF vars
    <2> QED  BY <2>1 DEF RS!vars, PosView, ResultView
  <1>1. CASE Next
    <2> USE <1>1 DEF Next, CConsume, ASink!Record
    <2>n. Len(log) \in 0..Len(Src)   BY DEF Inv, TypeOK
    <2>a. Len(log) < Len(Src)        OBVIOUS
    <2>b. last_hash' = Op(last_hash, Src[Len(log) + 1])   OBVIOUS
    <2>c. Len(log') = Len(log) + 1
      <3>1. log' = Append(log, [operation |-> Src[Len(log) + 1],
                               prev_hash |-> last_hash,
                               hash      |-> Op(last_hash, Src[Len(log) + 1])])
        OBVIOUS
      <3> QED  BY <3>1
    <2>1. PosView < Len(Src)               BY <2>a DEF PosView
    <2>2. ResultView' = Op(ResultView, Src[PosView + 1])
      BY <2>b DEF ResultView, PosView
    <2>3. PosView' = PosView + 1           BY <2>c DEF PosView
    <2>4. RS!Consume                       BY <2>1, <2>2, <2>3 DEF RS!Consume
    <2> QED  BY <2>4 DEF RS!Next
  <1> QED  BY <1>0, <1>1

THEOREM Refinement == Spec => RS!Spec
  <1>1. Init => RS!Init                              BY InitRefines
  <1>2. Inv /\ [Next]_vars => [RS!Next]_(RS!vars)    BY NextRefines
  <1>3. Spec => []Inv                                BY Safety
  <1> QED  BY <1>1, <1>2, <1>3, PTL DEF Spec, RS!Spec

THEOREM RefinementOriginal == Spec => ReductionStreamRefinement
  BY Refinement DEF ReductionStreamRefinement

====
