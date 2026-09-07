---- MODULE CompetitiveSelectionRanked_Proof ----
(* TLAPS proof of CompetitiveSelectionRanked safety.
   Proves Spec => [](TypeInvariant /\ BoundedMultiplicity /\ ThresholdOptimality
   /\ RankedTieBreak).

   Select is
   the unique top-K by score-then-Pos: selected' = {c \in Candidates :
   Rank(c) < K}, where Rank(c) counts the candidates strictly Better than c and
   Better is the score-desc-then-Pos-asc strict total order.  Pinning the
   tie-break makes this a constructive characterization. BoundedMultiplicity
   requires Better's trichotomy and transitivity together with Rank
   injectivity.  BoundedMultiplicity is discharged by cardinality-via-injection:
   Rank injects selected into 0..(K-1) (FS_Injection).  ThresholdOptimality and
   RankedTieBreak both fall out of the core Select fact (Rank(c) < Rank(d) =>
   Better(c,d), via trichotomy + the Rank-strict lemma).  The Pos machinery
   (WNType/WEnumBij/PosProp/PosInjective/PosNat) provides a fixed inverse
   enumeration for exact score ties. *)

EXTENDS CompetitiveSelectionRanked, FiniteSetTheorems, TLAPS

\* Candidate finiteness ensures
\* that selected \subseteq Candidates implies selected is finite, and so the
\* "strictly better" sets whose cardinality is Rank are finite.
ASSUME CandidatesFinite == IsFiniteSet(Candidates)

\* MaxScore is a natural score bound.
ASSUME MaxScoreType == MaxScore \in Nat

\* ----------------------------------------------------------------------
\* WN and WEnum assign a fixed position to every candidate for deterministic
\* lowest-position tie-breaking.
\* ----------------------------------------------------------------------
LEMMA WNType == WN \in Nat
  BY CandidatesFinite, FS_CardinalityType DEF WN

LEMMA WEnumBij ==
  /\ WEnum \in [1..WN -> Candidates]
  /\ \A c \in Candidates : \E i \in 1..WN : WEnum[i] = c
  /\ \A i \in 1..WN : \A j \in 1..WN : WEnum[i] = WEnum[j] => i = j
  <1> DEFINE Q(seq) == \A c \in Candidates : \E i \in 1..WN : seq[i] = c
  <1>card. Cardinality(Candidates) = WN  BY DEF WN
  <1>bij. ExistsBijection(1..WN, Candidates)
    BY CandidatesFinite, FS_CardinalityType, <1>card
  <1>ex. \E seq \in [1..WN -> Candidates] : Q(seq)
    <2>1. PICK f \in Bijection(1..WN, Candidates) : TRUE
      BY <1>bij DEF ExistsBijection
    <2>2. f \in Surjection(1..WN, Candidates)  BY <2>1 DEF Bijection
    <2>3. f \in [1..WN -> Candidates] /\ Q(f)  BY <2>2 DEF Surjection
    <2> QED  BY <2>3
  <1>1. WEnum \in [1..WN -> Candidates] /\ Q(WEnum)
    BY CandidateOrderType DEF WEnum
  <1>fin. IsFiniteSet(1..WN)  BY WNType, FS_Interval
  <1>surj. WEnum \in Surjection(1..WN, Candidates)
    BY <1>1 DEF Surjection
  <1>cc. Cardinality(1..WN) = Cardinality(Candidates)
    <2>1. Cardinality(1..WN) = WN  BY WNType, FS_Interval
    <2> QED  BY <2>1, <1>card
  <1>inj. WEnum \in Injection(1..WN, Candidates)
    BY <1>surj, <1>fin, <1>cc, FS_Surjection
  <1>2. \A i \in 1..WN : \A j \in 1..WN : WEnum[i] = WEnum[j] => i = j
    BY <1>inj DEF Injection, IsInjective
  <1> QED  BY CandidateOrderType, <1>1, <1>2 DEF WEnum

LEMMA PosProp ==
  ASSUME NEW c \in Candidates
  PROVE  /\ Pos(c) \in 1..WN
         /\ WEnum[Pos(c)] = c
  <1>1. \E i \in 1..WN : WEnum[i] = c  BY WEnumBij
  <1> QED  BY <1>1 DEF Pos

\* Pos is WEnum's inverse; distinct candidates have distinct positions.
LEMMA PosInjective ==
  ASSUME NEW c \in Candidates, NEW d \in Candidates, c # d
  PROVE  Pos(c) # Pos(d)
  <1> SUFFICES ASSUME Pos(c) = Pos(d) PROVE FALSE  OBVIOUS
  <1>1. WEnum[Pos(c)] = c  BY PosProp
  <1>2. WEnum[Pos(d)] = d  BY PosProp
  <1> QED  BY <1>1, <1>2

LEMMA PosNat ==
  ASSUME NEW c \in Candidates
  PROVE  Pos(c) \in Nat
  <1>1. Pos(c) \in 1..WN  BY PosProp
  <1> QED  BY <1>1, WNType, FS_Interval

\* ----------------------------------------------------------------------
\* Better is the score-descending, position-ascending strict total order.
\* ----------------------------------------------------------------------

\* Better implies weak score dominance: used for ThresholdOptimality.
LEMMA BetterImpliesGE ==
  ASSUME NEW c \in Candidates, NEW d \in Candidates,
         scores[c] \in Nat, scores[d] \in Nat, Better(c, d)
  PROVE  scores[c] >= scores[d]
  BY DEF Better

\* Irreflexivity: no candidate is Better than itself.
LEMMA BetterIrrefl ==
  ASSUME NEW c \in Candidates, scores[c] \in Nat
  PROVE  ~ Better(c, c)
  <1>1. Pos(c) \in Nat  BY PosNat
  <1> QED  BY <1>1 DEF Better

\* For distinct candidates, exactly one of Better(c,d), Better(d,c) holds.
\* Natural score order decides unequal scores; Pos decides exact ties.
LEMMA BetterTrichotomy ==
  ASSUME NEW c \in Candidates, NEW d \in Candidates, c # d,
         scores[c] \in Nat, scores[d] \in Nat
  PROVE  /\ Better(c, d) \/ Better(d, c)
         /\ ~ (Better(c, d) /\ Better(d, c))
  <1>pos. Pos(c) # Pos(d)  BY PosInjective
  <1>posnat. Pos(c) \in Nat /\ Pos(d) \in Nat  BY PosNat
  <1>postri. Pos(c) < Pos(d) \/ Pos(d) < Pos(c)  BY <1>pos, <1>posnat
  <1>tri. \/ scores[c] > scores[d]
          \/ scores[c] = scores[d]
          \/ scores[d] > scores[c]
    OBVIOUS
  <1>gt. CASE scores[c] > scores[d]
    <2>1. Better(c, d)  BY <1>gt DEF Better
    <2>2. ~ Better(d, c)  BY <1>gt DEF Better
    <2> QED  BY <2>1, <2>2
  <1>eq. CASE scores[c] = scores[d]
    <2>a. CASE Pos(c) < Pos(d)
      <3>1. Better(c, d)  BY <1>eq, <2>a DEF Better
      <3>2. ~ Better(d, c)  BY <1>eq, <2>a, <1>posnat DEF Better
      <3> QED  BY <3>1, <3>2
    <2>b. CASE Pos(d) < Pos(c)
      <3>1. Better(d, c)  BY <1>eq, <2>b DEF Better
      <3>2. ~ Better(c, d)  BY <1>eq, <2>b, <1>posnat DEF Better
      <3> QED  BY <3>1, <3>2
    <2> QED  BY <1>postri, <2>a, <2>b
  <1>lt. CASE scores[d] > scores[c]
    <2>1. Better(d, c)  BY <1>lt DEF Better
    <2>2. ~ Better(c, d)  BY <1>lt DEF Better
    <2> QED  BY <2>1, <2>2
  <1> QED  BY <1>tri, <1>gt, <1>eq, <1>lt

\* Transitivity: Better(c,d) /\ Better(d,e) => Better(c,e).  A direct
\* score/position case analysis (no three-term product argument): a strictly
\* higher score dominates; equal scores chain through Pos's own transitivity.
LEMMA BetterTrans ==
  ASSUME NEW c \in Candidates, NEW d \in Candidates, NEW e \in Candidates,
         scores[c] \in Nat, scores[d] \in Nat, scores[e] \in Nat,
         Better(c, d), Better(d, e)
  PROVE  Better(c, e)
  <1>pc. Pos(c) \in Nat  BY PosNat
  <1>pd. Pos(d) \in Nat  BY PosNat
  <1>pe. Pos(e) \in Nat  BY PosNat
  <1> QED  BY <1>pc, <1>pd, <1>pe DEF Better

\* ----------------------------------------------------------------------
\* Rank: the number of candidates strictly Better than c.  Because Better is a
\* strict total order over finite Candidates, Rank is injective onto 0..(WN-1).
\* ----------------------------------------------------------------------

\* Rank is a natural (cardinality of a finite subset of Candidates).
LEMMA RankNat ==
  ASSUME NEW c \in Candidates
  PROVE  Rank(c) \in Nat
  <1>sub. {d \in Candidates : Better(d, c)} \subseteq Candidates  OBVIOUS
  <1>fin. IsFiniteSet({d \in Candidates : Better(d, c)})
    BY <1>sub, CandidatesFinite, FS_Subset
  <1> QED  BY <1>fin, FS_CardinalityType DEF Rank

\* Rank-strict: Better(c,d) => Rank(c) < Rank(d).  {e : Better(e,c)} is a PROPER
\* subset of {e : Better(e,d)}: transitivity gives the subset (Better(e,c) /\
\* Better(c,d) => Better(e,d)); Better(c,d) puts c in the larger set and
\* irreflexivity keeps c out of the smaller, giving strictness.  The
\* cardinality-of-proper-subset step is FS_RemoveElement + FS_Subset.
LEMMA RankStrict ==
  ASSUME \A x \in Candidates : scores[x] \in Nat,
         NEW c \in Candidates, NEW d \in Candidates, Better(c, d)
  PROVE  Rank(c) < Rank(d)
  <1> DEFINE A == {x \in Candidates : Better(x, c)}
  <1> DEFINE B == {x \in Candidates : Better(x, d)}
  <1>cnat. scores[c] \in Nat  OBVIOUS
  <1>dnat. scores[d] \in Nat  OBVIOUS
  <1>subAB. A \subseteq B
    <2> SUFFICES ASSUME NEW x \in A PROVE x \in B  OBVIOUS
    <2>xC. x \in Candidates  OBVIOUS
    <2>bxc. Better(x, c)  OBVIOUS
    <2>xnat. scores[x] \in Nat  BY <2>xC
    <2>bxd. Better(x, d)
      BY <2>xC, <2>bxc, <1>cnat, <1>dnat, <2>xnat, BetterTrans
    <2> QED  BY <2>xC, <2>bxd
  <1>cInB. c \in B  BY Better(c, d)
  <1>cNotInA. c \notin A  BY <1>cnat, BetterIrrefl
  <1>subABc. A \subseteq (B \ {c})  BY <1>subAB, <1>cNotInA
  <1>subB. B \subseteq Candidates  OBVIOUS
  <1>finB. IsFiniteSet(B)  BY <1>subB, CandidatesFinite, FS_Subset
  <1>finBc. Cardinality(B \ {c}) = Cardinality(B) - 1
    BY <1>cInB, <1>finB, FS_RemoveElement
  <1>finBcFin. IsFiniteSet(B \ {c})  BY <1>finB, FS_RemoveElement
  <1>cardA. Cardinality(A) <= Cardinality(B \ {c})
    BY <1>subABc, <1>finBcFin, FS_Subset
  <1>cardBnat. Cardinality(B) \in Nat  BY <1>finB, FS_CardinalityType
  <1>subA. A \subseteq Candidates  OBVIOUS
  <1>finA. IsFiniteSet(A)  BY <1>subA, CandidatesFinite, FS_Subset
  <1>cardAnat. Cardinality(A) \in Nat  BY <1>finA, FS_CardinalityType
  <1>le. Cardinality(A) <= Cardinality(B) - 1  BY <1>cardA, <1>finBc, <1>cardBnat
  <1>lt. Cardinality(A) < Cardinality(B)  BY <1>le, <1>cardAnat, <1>cardBnat
  <1>rc. Rank(c) = Cardinality(A)  BY DEF Rank
  <1>rd. Rank(d) = Cardinality(B)  BY DEF Rank
  <1> QED  BY <1>lt, <1>rc, <1>rd

\* Rank injectivity: distinct candidates get distinct Ranks.  From trichotomy
\* (one of Better(c,d), Better(d,c) holds) and Rank-strict.
LEMMA RankInjective ==
  ASSUME \A x \in Candidates : scores[x] \in Nat,
         NEW c \in Candidates, NEW d \in Candidates, c # d
  PROVE  Rank(c) # Rank(d)
  <1>cnat. scores[c] \in Nat  OBVIOUS
  <1>dnat. scores[d] \in Nat  OBVIOUS
  <1>rcNat. Rank(c) \in Nat  BY RankNat
  <1>rdNat. Rank(d) \in Nat  BY RankNat
  <1>tri. Better(c, d) \/ Better(d, c)
    BY <1>cnat, <1>dnat, BetterTrichotomy
  <1>A. CASE Better(c, d)
    <2>1. Rank(c) < Rank(d)  BY <1>A, RankStrict
    <2> QED  BY <2>1, <1>rcNat, <1>rdNat
  <1>B. CASE Better(d, c)
    <2>1. Rank(d) < Rank(c)  BY <1>B, RankStrict
    <2> QED  BY <2>1, <1>rcNat, <1>rdNat
  <1> QED  BY <1>tri, <1>A, <1>B

\* A size-K set satisfying the exported tie-order contract is the canonical
\* Rank-below-K set. This is the bridge used by the executable refinement:
\* Verus promises exact cardinality plus RankedTieBreak rather than mentioning
\* the TLA+ Rank helper directly.
LEMMA ContractSelectStep ==
  ASSUME scores \in [Candidates -> 0..MaxScore],
         selected' \subseteq Candidates,
         Cardinality(selected') = K,
         \A c \in selected' : \A d \in Candidates \ selected' :
           Better(c, d)
  PROVE  selected' = {c \in Candidates : Rank(c) < K}
  <1> DEFINE Top == {c \in Candidates : Rank(c) < K}
  <1>scoresnat. \A x \in Candidates : scores[x] \in Nat
    BY MaxScoreType
  <1>selSub. selected' \subseteq Candidates  OBVIOUS
  <1>selFin. IsFiniteSet(selected')
    BY <1>selSub, CandidatesFinite, FS_Subset
  <1>left. selected' \subseteq Top
    <2> SUFFICES ASSUME NEW c \in selected' PROVE c \in Top  OBVIOUS
    <2>cC. c \in Candidates  BY <1>selSub
    <2> DEFINE B == {d \in Candidates : Better(d, c)}
    <2>bSub. B \subseteq (selected' \ {c})
      <3> SUFFICES ASSUME NEW d \in B PROVE d \in (selected' \ {c})  OBVIOUS
      <3>dC. d \in Candidates  OBVIOUS
      <3>bdc. Better(d, c)  OBVIOUS
      <3>dc. d # c
        <4> SUFFICES ASSUME d = c PROVE FALSE  OBVIOUS
        <4> QED  BY <3>bdc, <2>cC, <1>scoresnat, BetterIrrefl
      <3>din. d \in selected'
        <4> SUFFICES ASSUME d \notin selected' PROVE FALSE  OBVIOUS
        <4>bcd. Better(c, d)
          OBVIOUS
        <4>rdc. Rank(d) < Rank(c)
          BY <1>scoresnat, <3>dC, <2>cC, <3>bdc, RankStrict
        <4>rcd. Rank(c) < Rank(d)
          BY <1>scoresnat, <2>cC, <3>dC, <4>bcd, RankStrict
        <4>rcNat. Rank(c) \in Nat  BY <2>cC, RankNat
        <4>rdNat. Rank(d) \in Nat  BY <3>dC, RankNat
        <4> QED  BY <4>rdc, <4>rcd, <4>rcNat, <4>rdNat
      <3> QED  BY <3>din, <3>dc
    <2>minusFin. IsFiniteSet(selected' \ {c})
      BY <1>selFin, FS_RemoveElement
    <2>cardB. Cardinality(B) <= Cardinality(selected' \ {c})
      BY <2>bSub, <2>minusFin, FS_Subset
    <2>cardMinus. Cardinality(selected' \ {c}) = K - 1
      BY <1>selFin, FS_RemoveElement
    <2>rankEq. Rank(c) = Cardinality(B)  BY DEF Rank
    <2>rankNat. Rank(c) \in Nat  BY <2>cC, RankNat
    <2>kNat. K \in Nat  BY KType
    <2>rankLt. Rank(c) < K
      BY <2>cardB, <2>cardMinus, <2>rankEq, <2>rankNat, <2>kNat, KType
    <2> QED  BY <2>cC, <2>rankLt DEF Top
  <1>right. Top \subseteq selected'
    <2> SUFFICES ASSUME NEW c \in Top PROVE c \in selected'  OBVIOUS
    <2>cC. c \in Candidates  OBVIOUS
    <2>rankLt. Rank(c) < K  OBVIOUS
    <2>contra. c \in selected'
      <3> SUFFICES ASSUME c \notin selected' PROVE FALSE  OBVIOUS
      <3>cNotIn. c \notin selected'  OBVIOUS
      <3> DEFINE B == {d \in Candidates : Better(d, c)}
      <3>selB. selected' \subseteq B
        <4> SUFFICES ASSUME NEW s \in selected' PROVE s \in B  OBVIOUS
        <4>sC. s \in Candidates  BY <1>selSub
        <4>bsc. Better(s, c)
          OBVIOUS
        <4> QED  BY <4>sC, <4>bsc
      <3>bSub. B \subseteq Candidates  OBVIOUS
      <3>bFin. IsFiniteSet(B)
        BY <3>bSub, CandidatesFinite, FS_Subset
      <3>cardLe. Cardinality(selected') <= Cardinality(B)
        BY <3>selB, <3>bFin, FS_Subset
      <3>rankEq. Rank(c) = Cardinality(B)  BY DEF Rank
      <3>kLeRank. K <= Rank(c)
        BY <3>cardLe, <3>rankEq
      <3>rankNat. Rank(c) \in Nat  BY <2>cC, RankNat
      <3>kNat. K \in Nat  BY KType
      <3> QED  BY <3>kLeRank, <2>rankLt, <3>rankNat, <3>kNat
    <2> QED  BY <2>contra
  <1> QED  BY <1>left, <1>right DEF Top

\* ----------------------------------------------------------------------
\* The combined inductive invariant.
\* ----------------------------------------------------------------------
Inv == TypeInvariant /\ BoundedMultiplicity /\ ThresholdOptimality /\ RankedTieBreak

\* ----------------------------------------------------------------------
\* Init satisfies Inv.
\* ----------------------------------------------------------------------
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    \* selected = {} \subseteq Candidates; scores \in [Cands -> 0..MaxScore].
    BY DEF Init, TypeInvariant
  <1>2. BoundedMultiplicity
    \* Cardinality({}) = 0 <= K.
    <2>1. selected = {}  BY DEF Init
    <2>2. Cardinality({}) = 0  BY FS_EmptySet
    <2> QED  BY <2>1, <2>2, KType DEF BoundedMultiplicity
  <1>3. ThresholdOptimality
    \* selected = {}, so the \A s \in selected quantifier is vacuous.
    BY DEF Init, ThresholdOptimality
  <1>4. RankedTieBreak
    \* selected = {}, so the \A c \in selected quantifier is vacuous.
    BY DEF Init, RankedTieBreak
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF Inv

\* ----------------------------------------------------------------------
\* Next preserves Inv by cases over Select and UpdateScores.
\* ----------------------------------------------------------------------
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, BoundedMultiplicity, ThresholdOptimality, RankedTieBreak
  <1>0. CASE UNCHANGED vars
    \* selected'=selected, scores'=scores; RankedTieBreak' needs Better' = Better
    \* (scores unchanged, Pos constant), so DEF Better is required here.
    BY <1>0 DEF vars, Better
  <1>A. CASE Select
    <2> SUFFICES ASSUME Select PROVE Inv'  BY <1>A
    <2>1. selected' = {c \in Candidates : Rank(c) < K}
      BY ContractSelectStep DEF Select, TypeInvariant
    <2>2. scores' = scores  BY DEF Select
    <2>scoresnat. \A x \in Candidates : scores[x] \in Nat
      BY MaxScoreType DEF TypeInvariant
    \* TypeInvariant': selected' \subseteq Candidates; scores' still typed.
    <2>3. TypeInvariant'
      <3>1. selected' \subseteq Candidates  BY <2>1
      <3>2. scores' \in [Candidates -> 0..MaxScore]  BY <2>2 DEF TypeInvariant
      <3> QED  BY <3>1, <3>2 DEF TypeInvariant
    \* The core Select fact: every selected candidate is Better than every
    \* non-selected one -- because Rank(selected) < K <= Rank(non-selected), and
    \* Rank(c) < Rank(d) forces Better(c,d) (trichotomy rules out c=d and
    \* Better(d,c), the latter via Rank-strict).  ThresholdOptimality' and
    \* RankedTieBreak' both reduce to this.
    <2>core. \A cx \in selected' : \A dx \in (Candidates \ selected') : Better(cx, dx)
      <3> SUFFICES ASSUME NEW cx \in selected', NEW dx \in (Candidates \ selected')
                   PROVE  Better(cx, dx)
        OBVIOUS
      <3>cxC. cx \in Candidates  BY <2>1
      <3>dxC. dx \in Candidates  OBVIOUS
      <3>rcx. Rank(cx) < K  BY <2>1
      <3>rdx. ~ (Rank(dx) < K)  BY <2>1, <3>dxC
      <3>rcxNat. Rank(cx) \in Nat  BY <3>cxC, RankNat
      <3>rdxNat. Rank(dx) \in Nat  BY <3>dxC, RankNat
      <3>rlt. Rank(cx) < Rank(dx)  BY <3>rcx, <3>rdx, <3>rcxNat, <3>rdxNat, KType
      <3>cxnat. scores[cx] \in Nat  BY <2>scoresnat, <3>cxC
      <3>dxnat. scores[dx] \in Nat  BY <2>scoresnat, <3>dxC
      <3>ne. cx # dx
        <4> SUFFICES ASSUME cx = dx PROVE FALSE  OBVIOUS
        <4>1. Rank(cx) = Rank(dx)  OBVIOUS  \* cx = dx
        <4> QED  BY <4>1, <3>rlt, <3>rcxNat
      <3>tri. Better(cx, dx) \/ Better(dx, cx)
        BY <3>cxC, <3>dxC, <3>ne, <3>cxnat, <3>dxnat, BetterTrichotomy
      <3>notrev. ~ Better(dx, cx)
        <4> SUFFICES ASSUME Better(dx, cx) PROVE FALSE  OBVIOUS
        <4>1. Rank(dx) < Rank(cx)
          BY <2>scoresnat, <3>cxC, <3>dxC, RankStrict
        <4> QED  BY <4>1, <3>rlt, <3>rcxNat, <3>rdxNat
      <3> QED  BY <3>tri, <3>notrev
    \* BoundedMultiplicity': Rank injects selected' into 0..(K-1), a size-K set.
    <2>4. BoundedMultiplicity'
      <3> DEFINE sel == {c \in Candidates : Rank(c) < K}
      <3>seleq. selected' = sel  BY <2>1
      <3>selsub. sel \subseteq Candidates  OBVIOUS
      <3>selfin. IsFiniteSet(sel)  BY <3>selsub, CandidatesFinite, FS_Subset
      <3> DEFINE rankFn == [c \in sel |-> Rank(c)]
      <3>fnType. rankFn \in [sel -> 0..(K-1)]
        <4>a. \A c \in sel : Rank(c) \in 0..(K-1)
          <5> SUFFICES ASSUME NEW c \in sel PROVE Rank(c) \in 0..(K-1)  OBVIOUS
          <5>1. c \in Candidates  BY <3>selsub
          <5>2. Rank(c) < K  OBVIOUS
          <5>3. Rank(c) \in Nat  BY <5>1, RankNat
          <5> QED  BY <5>2, <5>3, KType
        <4> QED  BY <4>a DEF rankFn
      <3>inj. IsInjective(rankFn)
        <4> SUFFICES ASSUME NEW a \in sel, NEW b \in sel, rankFn[a] = rankFn[b]
                     PROVE  a = b
          BY DEF IsInjective
        <4>1. Rank(a) = Rank(b)  BY DEF rankFn
        <4>aC. a \in Candidates  BY <3>selsub
        <4>bC. b \in Candidates  BY <3>selsub
        <4> QED  BY <4>1, <4>aC, <4>bC, <2>scoresnat, RankInjective
      <3>rankInj. rankFn \in Injection(sel, 0..(K-1))
        BY <3>fnType, <3>inj DEF Injection
      <3>kint. (K - 1) \in Int  BY KType
      <3>finInt. IsFiniteSet(0..(K-1))  BY <3>kint, FS_Interval
      <3>cardLe. Cardinality(sel) <= Cardinality(0..(K-1))
        BY <3>rankInj, <3>finInt, FS_Injection
      <3>cardInt. Cardinality(0..(K-1)) = K
        BY <3>kint, KType, FS_Interval
      <3> QED  BY <3>seleq, <3>cardLe, <3>cardInt DEF BoundedMultiplicity
    \* ThresholdOptimality': Better(cx,dx) => scores[cx] >= scores[dx]; scores unchanged.
    <2>5. ThresholdOptimality'
      <3> SUFFICES ASSUME NEW s \in selected', NEW cc \in Candidates \ selected'
                   PROVE  scores'[s] >= scores'[cc]
        BY DEF ThresholdOptimality
      <3>sC. s \in Candidates  BY <2>1
      <3>ccC. cc \in Candidates  OBVIOUS
      <3>better. Better(s, cc)  BY <2>core
      <3>snat. scores[s] \in Nat  BY <2>scoresnat, <3>sC
      <3>ccnat. scores[cc] \in Nat  BY <2>scoresnat, <3>ccC
      <3>ge. scores[s] >= scores[cc]  BY <3>better, <3>sC, <3>ccC, <3>snat, <3>ccnat, BetterImpliesGE
      <3> QED  BY <3>ge, <2>2
    \* RankedTieBreak': the core fact directly, transported through scores' = scores.
    <2>6. RankedTieBreak'
      <3> SUFFICES ASSUME NEW cx \in selected', NEW dx \in Candidates \ selected'
                   PROVE  Better(cx, dx)'
        BY DEF RankedTieBreak
      <3>1. Better(cx, dx)  BY <2>core
      <3> QED  BY <3>1, <2>2 DEF Better
    <2> QED  BY <2>3, <2>4, <2>5, <2>6 DEF Inv
  <1>B. CASE UpdateScores
    \* selected' = {} (Bounded vacuous, Threshold + TieBreak vacuous); scores' typed.
    <2> SUFFICES ASSUME UpdateScores PROVE Inv'  BY <1>B
    <2>1. selected' = {}                     BY DEF UpdateScores
    <2>2. PICK new_scores \in [Candidates -> 0..MaxScore] : scores' = new_scores
      BY DEF UpdateScores
    <2>3. TypeInvariant'
      <3>1. selected' \subseteq Candidates  BY <2>1
      <3>2. scores' \in [Candidates -> 0..MaxScore]  BY <2>2
      <3> QED  BY <3>1, <3>2 DEF TypeInvariant
    <2>4. BoundedMultiplicity'
      <3>1. Cardinality(selected') = 0  BY <2>1, FS_EmptySet
      <3> QED  BY <3>1, KType DEF BoundedMultiplicity
    <2>5. ThresholdOptimality'
      \* \A s \in {} : ... is vacuous.
      BY <2>1 DEF ThresholdOptimality
    <2>6. RankedTieBreak'
      \* \A c \in {} : ... is vacuous.
      BY <2>1 DEF RankedTieBreak
    <2> QED  BY <2>3, <2>4, <2>5, <2>6 DEF Inv
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B DEF Next
  <1> QED  BY <1>0, <1>X

\* ----------------------------------------------------------------------
\* The safety theorem and per-invariant corollaries.
\* ----------------------------------------------------------------------
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv               BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant         BY Safety, PTL DEF Inv
THEOREM BoundedMultiplicitySafety == Spec => []BoundedMultiplicity  BY Safety, PTL DEF Inv
THEOREM ThresholdOptimalitySafety == Spec => []ThresholdOptimality  BY Safety, PTL DEF Inv
THEOREM RankedTieBreakSafety == Spec => []RankedTieBreak  BY Safety, PTL DEF Inv
====
