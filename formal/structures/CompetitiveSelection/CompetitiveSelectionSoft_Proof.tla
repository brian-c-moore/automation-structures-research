---- MODULE CompetitiveSelectionSoft_Proof ----
(* TLAPS proof of CompetitiveSelectionSoft safety: TypeInvariant,
   NonNegativity, BoundedTotal, Normalization, UniversalContribution,
   ScoreOrderPreservation, TieBoundedness.

   The construction derives weights from an evolving extra via a Pool-step
   sequential Webster/Sainte-Lague award process. Winner is
   at every AssignNext step, the awarded candidate is the one with highest
   priority scores[c] / (2*extra[c]+1), compared by cross-multiplication.
   Establishing that Winner has this property requires proving a
   maximum exists under Prefer, which in turn requires Prefer's transitivity
   by chaining cross-multiplied ratio comparisons through a three-term
   product. MulMonoNonStrict supplies the required multiplication monotonicity. *)
EXTENDS CompetitiveSelectionSoft, Naturals, FiniteSets, FiniteSetTheorems,
        NaturalsInduction, TLAPS

ASSUME CandidatesFinite == IsFiniteSet(Candidates)
ASSUME CandidatesNonempty == Candidates # {}
ASSUME WeightTotalType == WeightTotal \in Nat
ASSUME MaxScoreType == MaxScore \in Nat

\* ---- WN, and the bijective enumeration WEnum -----------------------------
LEMMA WNType == WN \in Nat
  BY CandidatesFinite, FS_CardinalityType DEF WN

LEMMA WNPos == WN \in Nat /\ WN > 0
  <1>1. WN \in Nat  BY WNType
  <1>2. WN = 0 => Candidates = {}
    <2> SUFFICES ASSUME WN = 0 PROVE Candidates = {}  OBVIOUS
    <2>1. Cardinality(Candidates) = 0  BY DEF WN
    <2> QED  BY <2>1, CandidatesFinite, FS_EmptySet
  <1> QED  BY <1>1, <1>2, CandidatesNonempty

LEMMA WNConst == WN' = WN
  BY DEF WN

LEMMA WEnumConst == WEnum' = WEnum
  BY DEF WEnum

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

\* Pos is WEnum's inverse: distinct candidates get distinct positions.
LEMMA PosProp ==
  ASSUME NEW c \in Candidates
  PROVE  /\ Pos(c) \in 1..WN
         /\ WEnum[Pos(c)] = c
  <1>1. \E i \in 1..WN : WEnum[i] = c  BY WEnumBij
  <1> QED  BY <1>1 DEF Pos

LEMMA PosInjective ==
  ASSUME NEW c \in Candidates, NEW d \in Candidates, c # d
  PROVE  Pos(c) # Pos(d)
  <1> SUFFICES ASSUME Pos(c) = Pos(d) PROVE FALSE  OBVIOUS
  <1>1. WEnum[Pos(c)] = c  BY PosProp
  <1>2. WEnum[Pos(d)] = d  BY PosProp
  <1> QED  BY <1>1, <1>2

\* ---- Core nonlinear-arithmetic building block ----------------------------
\* Multiplication monotonicity over naturals; the cancellation lemmas below
\* derive from this induction and positivity of the common factor.
LEMMA MulMonoNonStrict ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, a <= b
  PROVE  a * c <= b * c
  <1> DEFINE P(k) == k \in Nat => a * k <= b * k
  <1>1. P(0)  OBVIOUS
  <1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
    <2> SUFFICES ASSUME k + 1 \in Nat PROVE a * (k + 1) <= b * (k + 1)  OBVIOUS
    <2>1. a * (k + 1) = a * k + a  OBVIOUS
    <2>2. b * (k + 1) = b * k + b  OBVIOUS
    <2>3. a * k <= b * k  BY P(k)
    <2> QED  BY <2>1, <2>2, <2>3, a <= b
  <1>3. \A k \in Nat : P(k)  BY <1>1, <1>2, NatInduction
  <1> QED  BY <1>3

LEMMA MulStrictMono ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, a < b, c > 0
  PROVE  a * c < b * c
  <1>1. a + 1 <= b  OBVIOUS
  <1>2. (a + 1) * c <= b * c  BY <1>1, MulMonoNonStrict
  <1>3. (a + 1) * c = a * c + c  OBVIOUS
  <1> QED  BY <1>2, <1>3, c > 0

LEMMA MulCancelPos ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, a * c > b * c, c > 0
  PROVE  a > b
  <1> SUFFICES ASSUME a <= b PROVE FALSE  OBVIOUS
  <1>1. a * c <= b * c  BY MulMonoNonStrict
  <1> QED  BY <1>1, a * c > b * c

LEMMA MulCancelNonStrict ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, a * c >= b * c, c > 0
  PROVE  a >= b
  <1> SUFFICES ASSUME a < b PROVE FALSE  OBVIOUS
  <1>1. a * c < b * c  BY MulStrictMono
  <1> QED  BY <1>1, a * c >= b * c

LEMMA MulCancelEq ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, a * c = b * c, c > 0
  PROVE  a = b
  <1>1. b * c >= a * c  BY a * c = b * c
  <1>2. b >= a  BY <1>1, MulCancelNonStrict
  <1>3. a * c >= b * c  BY a * c = b * c
  <1>4. a >= b  BY <1>3, MulCancelNonStrict
  <1> QED  BY <1>2, <1>4

\* Named natural-order case lemmas used by the cross-product proofs.
LEMMA NatTrichotomy ==
  ASSUME NEW a \in Nat, NEW b \in Nat
  PROVE  a > b \/ a = b \/ a < b
  OBVIOUS

LEMMA NatLECases ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a <= b
  PROVE  a < b \/ a = b
  OBVIOUS

\* ---- Prefer: the tie-broken cross-multiplied priority order ---------------
\* Both disjuncts of Prefer give the non-strict cross-multiplied inequality;
\* collapsing to this one fact avoids re-splitting on the disjunction in
\* every downstream lemma.  Stated with <= (matching MulMonoNonStrict's own
\* conclusion shape) rather than >=, so later citations need no reorientation.
LEMMA PreferImpliesGE ==
  ASSUME NEW c \in Candidates, NEW d \in Candidates,
         scores[c] \in Nat, scores[d] \in Nat, extra[c] \in Nat, extra[d] \in Nat,
         Prefer(c, d)
  PROVE  scores[d] * (2 * extra[c] + 1) <= scores[c] * (2 * extra[d] + 1)
  BY DEF Prefer

LEMMA PreferIrrefl ==
  ASSUME NEW c \in Candidates, scores[c] \in Nat, extra[c] \in Nat
  PROVE  ~ Prefer(c, c)
  BY DEF Prefer

\* For distinct candidates, exactly one of Prefer(c,d), Prefer(d,c) holds:
\* the cross-multiplied terms are Nat, so trichotomy of >/=/< applies, and
\* when they tie exactly, Pos(c) # Pos(d) resolves it one way or the other
\* (position trichotomy, since Pos values are distinct naturals).
LEMMA PreferTrichotomy ==
  ASSUME NEW c \in Candidates, NEW d \in Candidates, c # d,
         scores[c] \in Nat, scores[d] \in Nat, extra[c] \in Nat, extra[d] \in Nat
  PROVE  /\ Prefer(c, d) \/ Prefer(d, c)
         /\ ~ (Prefer(c, d) /\ Prefer(d, c))
  <1>pos. Pos(c) # Pos(d)  BY PosInjective
  <1>posc. Pos(c) \in 1..WN  BY PosProp
  <1>posd. Pos(d) \in 1..WN  BY PosProp
  <1>poscnat. Pos(c) \in Nat  BY <1>posc
  <1>posdnat. Pos(d) \in Nat  BY <1>posd
  <1>posnat. Pos(c) \in Nat /\ Pos(d) \in Nat  BY <1>poscnat, <1>posdnat
  <1>postri. Pos(c) < Pos(d) \/ Pos(d) < Pos(c)  BY <1>pos, <1>posnat
  <1>lhs. scores[c] * (2 * extra[d] + 1) \in Nat  OBVIOUS
  <1>rhs. scores[d] * (2 * extra[c] + 1) \in Nat  OBVIOUS
  <1>tri. \/ scores[c] * (2 * extra[d] + 1) > scores[d] * (2 * extra[c] + 1)
          \/ scores[c] * (2 * extra[d] + 1) = scores[d] * (2 * extra[c] + 1)
          \/ scores[c] * (2 * extra[d] + 1) < scores[d] * (2 * extra[c] + 1)
    BY <1>lhs, <1>rhs, NatTrichotomy
  <1>gt. CASE scores[c] * (2 * extra[d] + 1) > scores[d] * (2 * extra[c] + 1)
    <2>1. Prefer(c, d)  BY <1>gt DEF Prefer
    <2>2. ~ Prefer(d, c)
      <3> SUFFICES ASSUME Prefer(d, c) PROVE FALSE  OBVIOUS
      <3> QED  BY <1>gt DEF Prefer
    <2> QED  BY <2>1, <2>2
  <1>eq. CASE scores[c] * (2 * extra[d] + 1) = scores[d] * (2 * extra[c] + 1)
    <2>a. CASE Pos(c) < Pos(d)
      <3>1. Prefer(c, d)  BY <1>eq, <2>a DEF Prefer
      <3>2. ~ Prefer(d, c)
        <4> SUFFICES ASSUME Prefer(d, c) PROVE FALSE  OBVIOUS
        <4>ngt. ~ (scores[d] * (2 * extra[c] + 1) > scores[c] * (2 * extra[d] + 1))
          BY <1>eq
        <4>neq. ~ (Pos(d) < Pos(c))
          BY <2>a, <1>posnat
        <4> QED  BY Prefer(d, c), <4>ngt, <4>neq DEF Prefer
      <3> QED  BY <3>1, <3>2
    <2>b. CASE Pos(d) < Pos(c)
      <3>1. Prefer(d, c)  BY <1>eq, <2>b DEF Prefer
      <3>2. ~ Prefer(c, d)
        <4> SUFFICES ASSUME Prefer(c, d) PROVE FALSE  OBVIOUS
        <4>ngt. ~ (scores[c] * (2 * extra[d] + 1) > scores[d] * (2 * extra[c] + 1))
          BY <1>eq
        <4>neq. ~ (Pos(c) < Pos(d))
          BY <2>b, <1>posnat
        <4> QED  BY Prefer(c, d), <4>ngt, <4>neq DEF Prefer
      <3> QED  BY <3>1, <3>2
    <2> QED  BY <1>postri, <2>a, <2>b
  <1>lt. CASE scores[c] * (2 * extra[d] + 1) < scores[d] * (2 * extra[c] + 1)
    <2>1. Prefer(d, c)  BY <1>lt DEF Prefer
    <2>2. ~ Prefer(c, d)
      <3> SUFFICES ASSUME Prefer(c, d) PROVE FALSE  OBVIOUS
      <3> QED  BY <1>lt DEF Prefer
    <2> QED  BY <2>1, <2>2
  <1> QED  BY <1>tri, <1>gt, <1>eq, <1>lt

\* The core nonlinear fact: cross-multiplied priority comparison chains.
\* Prefer(c,d) /\ Prefer(d,e) => Prefer(c,e), via the three-term product
\* argument: multiply each hypothesis by the missing denominator, chain the
\* two resulting inequalities through their shared middle term, then cancel
\* the common positive factor.  Every step is stated as a <= between two
\* fully-parenthesized products, in the exact left/right shape
\* MulMonoNonStrict and MulCancelNonStrict expect, so citing them is a
\* direct instantiation and needs no reassociation.
LEMMA PreferTrans ==
  ASSUME NEW c \in Candidates, NEW d \in Candidates, NEW e \in Candidates,
         scores[c] \in Nat, scores[d] \in Nat, scores[e] \in Nat,
         extra[c] \in Nat, extra[d] \in Nat, extra[e] \in Nat,
         Prefer(c, d), Prefer(d, e)
  PROVE  Prefer(c, e)
  <1> DEFINE sc == scores[c]
  <1> DEFINE sd == scores[d]
  <1> DEFINE se == scores[e]
  <1> DEFINE A == 2 * extra[c] + 1
  <1> DEFINE B == 2 * extra[d] + 1
  <1> DEFINE C == 2 * extra[e] + 1
  <1>Anat. A \in Nat  OBVIOUS
  <1>Bnat. B \in Nat  OBVIOUS
  <1>Cnat. C \in Nat  OBVIOUS
  <1>Apos. A > 0  OBVIOUS
  <1>Bpos. B > 0  OBVIOUS
  <1>Cpos. C > 0  OBVIOUS
  <1>scnat. sc \in Nat  OBVIOUS
  <1>sdnat. sd \in Nat  OBVIOUS
  <1>senat. se \in Nat  OBVIOUS
  <1>i. sd * A <= sc * B  BY PreferImpliesGE
  <1>ii. se * B <= sd * C  BY PreferImpliesGE
  <1>sdA. sd * A \in Nat  OBVIOUS
  <1>scB. sc * B \in Nat  OBVIOUS
  <1>seB. se * B \in Nat  OBVIOUS
  <1>sdC. sd * C \in Nat  OBVIOUS
  <1>ip. (sd * A) * C <= (sc * B) * C
    BY <1>i, <1>Cnat, <1>sdA, <1>scB, MulMonoNonStrict
  <1>iip. (se * B) * A <= (sd * C) * A
    BY <1>ii, <1>Anat, <1>seB, <1>sdC, MulMonoNonStrict
  <1>reassoc1. (sd * A) * C = (sd * C) * A  OBVIOUS
  <1>mid1. (se * B) * A <= (sd * A) * C
    BY <1>iip, <1>reassoc1
  <1>reassoc2. (se * B) * A = (se * A) * B  OBVIOUS
  <1>reassoc3. (sc * B) * C = (sc * C) * B  OBVIOUS
  <1>chain2. (se * A) * B <= (sc * C) * B
    BY <1>mid1, <1>ip, <1>reassoc2, <1>reassoc3
  <1>seAnat. se * A \in Nat  OBVIOUS
  <1>scCnat. sc * C \in Nat  OBVIOUS
  <1>final. se * A <= sc * C
    BY <1>chain2, <1>seAnat, <1>scCnat, <1>Bpos, MulCancelNonStrict
  <1>exh. se * A < sc * C \/ se * A = sc * C
    BY <1>final, <1>seAnat, <1>scCnat, NatLECases
  \* The strict case closes directly.  The exact-tie case needs the sandwich
  \* argument: if the two ends of the chain (se*B)*A <= (sd*A)*C <= (sc*B)*C
  \* coincide, the middle term is pinned to both ends, which forces BOTH
  \* Prefer(c,d) and Prefer(d,e) to have fired via their equality branch --
  \* recovering the position facts each equality branch requires, and
  \* chaining those positions gives Prefer(c,e)'s own equality branch.
  <1>1. CASE se * A < sc * C
    <2> QED  BY <1>1 DEF Prefer
  <1>2. CASE se * A = sc * C
    <2>tieBC. (se * B) * A = (sc * B) * C
      BY <1>2, <1>reassoc2, <1>reassoc3
    <2>eqR. (sd * A) * C = (sc * B) * C
      BY <1>mid1, <1>ip, <2>tieBC, <1>sdA, <1>scB, <1>seAnat, <1>scCnat, <1>Cnat
    <2>eqL. (sd * A) * C = (se * B) * A
      BY <1>mid1, <1>ip, <2>tieBC, <1>sdA, <1>scB, <1>seAnat, <1>scCnat, <1>Cnat
    <2>sdAeqscB. sd * A = sc * B
      BY <2>eqR, <1>sdA, <1>scB, <1>Cnat, <1>Cpos, MulCancelEq
    <2>eqL2. (sd * C) * A = (se * B) * A
      BY <2>eqL, <1>reassoc1
    <2>seBeqsdC. se * B = sd * C
      <3>1. sd * C \in Nat  BY <1>sdC
      <3>2. se * B \in Nat  BY <1>seB
      <3> QED  BY <2>eqL2, <3>1, <3>2, <1>Anat, <1>Apos, MulCancelEq
    <2>posCD. Pos(c) < Pos(d)
      BY <2>sdAeqscB DEF Prefer
    <2>posDE. Pos(d) < Pos(e)
      BY <2>seBeqsdC DEF Prefer
    <2>poscnat. Pos(c) \in 1..WN  BY PosProp
    <2>posdnat. Pos(d) \in 1..WN  BY PosProp
    <2>posenat. Pos(e) \in 1..WN  BY PosProp
    <2>posCE. Pos(c) < Pos(e)
      BY <2>posCD, <2>posDE, <2>poscnat, <2>posdnat, <2>posenat, WNType, FS_Interval
    <2> QED  BY <1>2, <2>posCE DEF Prefer
  <1> QED  BY <1>exh, <1>1, <1>2

\* ---- Existence of a Prefer-maximum, hence Winner is well-defined ---------
\* Induction on Cardinality(T) removes one element per step while preserving
\* the subset-of-S domain required by the preference predicate.
LEMMA MaxExists ==
  ASSUME NEW S \in SUBSET Candidates, S # {},
         \A c \in Candidates : scores[c] \in Nat,
         \A c \in Candidates : extra[c] \in Nat
  PROVE  \E c \in S : \A d \in S \ {c} : Prefer(c, d)
  <1> DEFINE P(n) == \A T \in SUBSET S :
                       (Cardinality(T) = n /\ T # {})
                         => \E c \in T : \A d \in T \ {c} : Prefer(c, d)
  <1>1. P(0)
    <2> SUFFICES ASSUME NEW T \in SUBSET S, Cardinality(T) = 0, T # {}
                 PROVE  FALSE
      OBVIOUS
    <2>Tcand. T \in SUBSET Candidates  OBVIOUS
    <2>1. IsFiniteSet(T)  BY <2>Tcand, CandidatesFinite, FS_Subset
    <2>2. T = {}          BY <2>1, FS_EmptySet
    <2> QED  BY <2>2
  <1>2. ASSUME NEW n \in Nat, P(n)
        PROVE  P(n + 1)
    <2> SUFFICES ASSUME NEW T \in SUBSET S, Cardinality(T) = n + 1, T # {}
                 PROVE  \E c \in T : \A d \in T \ {c} : Prefer(c, d)
      BY DEF P
    <2>Tcand. T \in SUBSET Candidates  OBVIOUS
    <2>fin. IsFiniteSet(T)  BY <2>Tcand, CandidatesFinite, FS_Subset
    <2>x. PICK x \in T : TRUE  OBVIOUS
    <2>xInC. x \in Candidates  BY <2>x, <2>Tcand
    <2>xnat. scores[x] \in Nat /\ extra[x] \in Nat  BY <2>xInC
    <2> DEFINE Tp == T \ {x}
    <2>sub. Tp \in SUBSET S  OBVIOUS
    <2>subC. Tp \in SUBSET Candidates  OBVIOUS
    <2>card. Cardinality(Tp) = n
      BY <2>fin, <2>x, FS_RemoveElement
    <2>union. T = Tp \cup {x}  BY <2>x
    <2>A. CASE Tp = {}
      <3>1. T = {x}  BY <2>union, <2>A
      <3>2. \A d \in T \ {x} : Prefer(x, d)  BY <3>1
      <3> QED  BY <3>1, <3>2
    <2>B. CASE Tp # {}
      <3>1. \E c \in Tp : \A d \in Tp \ {c} : Prefer(c, d)
        BY <2>sub, <2>card, <2>B, P(n)
      <3>2. PICK cT \in Tp : \A d \in Tp \ {cT} : Prefer(cT, d)  BY <3>1
      <3>cTinTp. cT \in Tp  BY <3>2
      <3>cT. cT \in Candidates  BY <3>cTinTp, <2>subC
      <3>cTnat. scores[cT] \in Nat /\ extra[cT] \in Nat  BY <3>cT
      <3>cTx. cT # x  BY <3>cTinTp
      <3>tri. Prefer(cT, x) \/ Prefer(x, cT)
        BY <3>cT, <2>xInC, <3>cTx, <3>cTnat, <2>xnat, PreferTrichotomy
      <3>caseA. CASE Prefer(cT, x)
        <4>1. \A d \in Tp \ {cT} : Prefer(cT, d)  BY <3>2
        <4>2. Prefer(cT, x)  BY <3>caseA
        <4>3. \A d \in T \ {cT} : Prefer(cT, d)  BY <4>1, <4>2, <2>union
        <4> QED  BY <4>3, <3>cTinTp, <2>union
      <3>caseB. CASE Prefer(x, cT)
        <4>goal. \A d \in T \ {x} : Prefer(x, d)
          <5> SUFFICES ASSUME NEW d \in Tp PROVE Prefer(x, d)  BY <2>union
          <5>dc. CASE d = cT
            <6> QED  BY <5>dc, <3>caseB
          <5>dnc. CASE d # cT
            <6>d. d \in Candidates  BY <5>dc, <2>subC
            <6>dnat. scores[d] \in Nat /\ extra[d] \in Nat  BY <6>d
            <6>1. Prefer(cT, d)  BY <3>2, <5>dnc
            <6>2. Prefer(x, cT)  BY <3>caseB
            <6> QED
              BY <6>1, <6>2, <2>xInC, <3>cT, <6>d, <2>xnat, <3>cTnat, <6>dnat, PreferTrans
          <5> QED  BY <5>dc, <5>dnc
        <4> QED  BY <4>goal
      <3> QED  BY <3>tri, <3>caseA, <3>caseB
    <2> QED  BY <2>A, <2>B
  <1>step. \A n \in Nat : P(n) => P(n + 1)  BY <1>2
  <1>3. \A n \in Nat : P(n)  BY <1>1, <1>step, NatInduction
  <1>Scard. Cardinality(S) \in Nat  BY CandidatesFinite, FS_Subset, FS_CardinalityType
  <1>4. P(Cardinality(S))  BY <1>3, <1>Scard
  <1> QED  BY <1>4

LEMMA WinnerProp ==
  ASSUME \A c \in Candidates : scores[c] \in Nat,
         \A c \in Candidates : extra[c] \in Nat
  PROVE  Winner \in Candidates /\ \A d \in Candidates \ {Winner} : Prefer(Winner, d)
  <1>ex. \E c \in Candidates : \A d \in Candidates \ {c} : Prefer(c, d)
    BY MaxExists, CandidatesFinite, CandidatesNonempty
  <1> QED  BY <1>ex DEF Winner

\* ---- The crux: Prefer(c,d) forces extra[c] < extra[d] when scores[c] < scores[d],
\* and extra[c] <= extra[d] when scores[c] = scores[d].  This is what makes
\* every AssignNext step preserve ScoreOrderPreservation and TieBoundedness.
LEMMA PriorityStrict ==
  ASSUME NEW c \in Candidates, NEW d \in Candidates,
         scores[c] \in Nat, scores[d] \in Nat, extra[c] \in Nat, extra[d] \in Nat,
         scores[c] < scores[d],
         Prefer(c, d)
  PROVE  extra[c] < extra[d]
  <1> SUFFICES ASSUME extra[c] >= extra[d] PROVE FALSE  OBVIOUS
  <1>ge. scores[d] * (2 * extra[c] + 1) <= scores[c] * (2 * extra[d] + 1)
    BY PreferImpliesGE
  <1>xy. 2 * extra[d] + 1 <= 2 * extra[c] + 1  OBVIOUS
  <1>edpos. 2 * extra[d] + 1 > 0  OBVIOUS
  <1>a. scores[d] * (2 * extra[d] + 1) <= scores[d] * (2 * extra[c] + 1)
    BY <1>xy, MulMonoNonStrict
  <1>b. scores[c] * (2 * extra[d] + 1) < scores[d] * (2 * extra[d] + 1)
    BY MulStrictMono
  <1>chain. scores[c] * (2 * extra[d] + 1) < scores[d] * (2 * extra[c] + 1)
    BY <1>a, <1>b
  <1> QED  BY <1>ge, <1>chain

LEMMA PriorityTie ==
  ASSUME NEW c \in Candidates, NEW d \in Candidates,
         scores[c] \in Nat, scores[d] \in Nat, extra[c] \in Nat, extra[d] \in Nat,
         scores[c] = scores[d], scores[c] > 0,
         Prefer(c, d)
  PROVE  extra[c] <= extra[d]
  <1>ge. scores[d] * (2 * extra[c] + 1) <= scores[c] * (2 * extra[d] + 1)
    BY PreferImpliesGE
  <1>subst. scores[c] * (2 * extra[c] + 1) <= scores[c] * (2 * extra[d] + 1)
    BY <1>ge
  <1> QED  BY <1>subst, MulCancelNonStrict

\* ---- WSum recursion equation (current state and primed state) ------------
THEOREM WSumConcl ==
  FiniteNatInductiveDefConclusion(WSum, 0, LAMBDA p, i : p + weights[WEnum[i]], 0, WN)
  <1>1. FiniteNatInductiveDefHypothesis(WSum, 0, LAMBDA p, i : p + weights[WEnum[i]], 0, WN)
    BY DEF FiniteNatInductiveDefHypothesis, WSum
  <1> QED  BY <1>1, WNType, FiniteNatInductiveDef

LEMMA WSumRec ==
  WSum = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE WSum[i - 1] + weights[WEnum[i]]]
  BY WSumConcl DEF FiniteNatInductiveDefConclusion

THEOREM WSumConclPrime ==
  FiniteNatInductiveDefConclusion(WSum', 0, LAMBDA p, i : p + weights'[WEnum[i]], 0, WN)
  <1>1. FiniteNatInductiveDefHypothesis(WSum', 0, LAMBDA p, i : p + weights'[WEnum[i]], 0, WN)
    BY WNConst, WEnumConst DEF FiniteNatInductiveDefHypothesis, WSum
  <1> QED  BY <1>1, WNType, FiniteNatInductiveDef

LEMMA WSumRecPrime ==
  WSum' = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE WSum'[i - 1] + weights'[WEnum[i]]]
  BY WSumConclPrime DEF FiniteNatInductiveDefConclusion

\* ---- ExtraSum: the same fold, over extra directly, used by Terminal ------
THEOREM ExtraSumConcl ==
  FiniteNatInductiveDefConclusion(ExtraSum, 0, LAMBDA p, i : p + extra[WEnum[i]], 0, WN)
  <1>1. FiniteNatInductiveDefHypothesis(ExtraSum, 0, LAMBDA p, i : p + extra[WEnum[i]], 0, WN)
    BY DEF FiniteNatInductiveDefHypothesis, ExtraSum
  <1> QED  BY <1>1, WNType, FiniteNatInductiveDef

LEMMA ExtraSumRec ==
  ExtraSum = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE ExtraSum[i - 1] + extra[WEnum[i]]]
  BY ExtraSumConcl DEF FiniteNatInductiveDefConclusion

THEOREM ExtraSumConclPrime ==
  FiniteNatInductiveDefConclusion(ExtraSum', 0, LAMBDA p, i : p + extra'[WEnum[i]], 0, WN)
  <1>1. FiniteNatInductiveDefHypothesis(ExtraSum', 0, LAMBDA p, i : p + extra'[WEnum[i]], 0, WN)
    BY WNConst, WEnumConst DEF FiniteNatInductiveDefHypothesis, ExtraSum
  <1> QED  BY <1>1, WNType, FiniteNatInductiveDef

LEMMA ExtraSumRecPrime ==
  ExtraSum' = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE ExtraSum'[i - 1] + extra'[WEnum[i]]]
  BY ExtraSumConclPrime DEF FiniteNatInductiveDefConclusion

\* ---- Fold facts: typing, constant value, one-element delta, stability ----
LEMMA FoldRecStep ==
  ASSUME NEW vf, NEW F, NEW k \in Nat, k + 1 \in 0..WN,
         F = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE F[i - 1] + vf[WEnum[i]]]
  PROVE  F[k + 1] = F[k] + vf[WEnum[k + 1]]
  BY WNType

LEMMA FoldType ==
  ASSUME NEW g \in [Candidates -> Nat], NEW G,
         G = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE G[i - 1] + g[WEnum[i]]]
  PROVE  \A i \in 0..WN : G[i] \in Nat
  <1> USE WNType
  <1> DEFINE P(k) == k \in 0..WN => G[k] \in Nat
  <1>1. P(0)
    OBVIOUS
  <1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
    <2> SUFFICES ASSUME k + 1 \in 0..WN PROVE G[k + 1] \in Nat  OBVIOUS
    <2>k. k \in 0..WN  OBVIOUS
    <2>e. WEnum[k + 1] \in Candidates  BY WEnumBij
    <2>1. G[k + 1] = G[k] + g[WEnum[k + 1]]  BY <2>k
    <2>2. G[k] \in Nat  BY <2>k, P(k)
    <2>3. g[WEnum[k + 1]] \in Nat  BY <2>e
    <2> QED  BY <2>1, <2>2, <2>3
  <1>3. \A k \in Nat : P(k)  BY <1>1, <1>2, NatInduction
  <1> QED  BY <1>3

\* A value function constantly 1 folds to the running index: this is the
\* Init-time fact that WSum[WN] = Reserved (= WN), needed for BoundedTotal's
\* base case (Reserved <= WeightTotal, from the module's own ASSUME).
LEMMA FoldConstFn ==
  ASSUME NEW g \in [Candidates -> Nat], \A c \in Candidates : g[c] = 1,
         NEW G,
         G = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE G[i - 1] + g[WEnum[i]]]
  PROVE  \A i \in 0..WN : G[i] = i
  <1> USE WNType
  <1> DEFINE P(k) == k \in 0..WN => G[k] = k
  <1>1. P(0)
    OBVIOUS
  <1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
    <2> SUFFICES ASSUME k + 1 \in 0..WN PROVE G[k + 1] = k + 1  OBVIOUS
    <2>k. k \in 0..WN  OBVIOUS
    <2>e. WEnum[k + 1] \in Candidates  BY WEnumBij
    <2>gval. g[WEnum[k + 1]] = 1  BY <2>e
    <2>rec. G[k + 1] = G[k] + g[WEnum[k + 1]]  BY <2>k
    <2>ihv. G[k] = k  BY <2>k, P(k)
    <2> QED  BY <2>rec, <2>gval, <2>ihv
  <1>3. \A k \in Nat : P(k)  BY <1>1, <1>2, NatInduction
  <1> QED  BY <1>3

LEMMA FoldStable ==
  ASSUME NEW g \in [Candidates -> Nat], NEW G, NEW H,
         G = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE G[i - 1] + g[WEnum[i]]],
         H = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE H[i - 1] + g[WEnum[i]]]
  PROVE  H[WN] = G[WN]
  <1> USE WNType
  <1> DEFINE P(k) == k \in 0..WN => H[k] = G[k]
  <1>1. P(0)  OBVIOUS
  <1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
    <2> SUFFICES ASSUME k + 1 \in 0..WN PROVE H[k + 1] = G[k + 1]  OBVIOUS
    <2>k. k \in 0..WN  OBVIOUS
    <2>1. H[k + 1] = H[k] + g[WEnum[k + 1]]  BY <2>k
    <2>2. G[k + 1] = G[k] + g[WEnum[k + 1]]  BY <2>k
    <2>3. H[k] = G[k]  BY <2>k, P(k)
    <2> QED  BY <2>1, <2>2, <2>3
  <1>3. \A k \in Nat : P(k)  BY <1>1, <1>2, NatInduction
  <1> QED  BY <1>3, WNType

LEMMA WSumStable ==
  ASSUME extra \in [Candidates -> Nat], extra' = extra
  PROVE  WSum'[WN] = WSum[WN]
  <1>rec. WSum = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE WSum[i - 1] + weights[WEnum[i]]]
    BY WSumRec
  <1>recP. WSum' = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE WSum'[i - 1] + weights[WEnum[i]]]
    BY WSumRecPrime DEF weights
  <1> DEFINE P(k) == k \in 0..WN => WSum'[k] = WSum[k]
  <1>1. P(0)  BY <1>rec, <1>recP, WNType
  <1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
    <2> SUFFICES ASSUME k + 1 \in 0..WN PROVE WSum'[k + 1] = WSum[k + 1]
      OBVIOUS
    <2>k. k \in 0..WN  BY WNType
    <2>p. WSum'[k + 1] = WSum'[k] + weights[WEnum[k + 1]]
      BY <2>k, <1>recP
    <2>u. WSum[k + 1] = WSum[k] + weights[WEnum[k + 1]]
      BY <2>k, <1>rec
    <2>ih. WSum'[k] = WSum[k]  BY <2>k, P(k)
    <2> QED  BY <2>p, <2>u, <2>ih
  <1>3. \A k \in Nat : P(k)  BY <1>1, <1>2, NatInduction
  <1> QED  BY <1>3, WNType

LEMMA ExtraSumStable ==
  ASSUME extra \in [Candidates -> Nat], extra' = extra
  PROVE  ExtraSum'[WN] = ExtraSum[WN]
  <1>rec. ExtraSum = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE ExtraSum[i - 1] + extra[WEnum[i]]]
    BY ExtraSumRec
  <1>recP. ExtraSum' = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE ExtraSum'[i - 1] + extra[WEnum[i]]]
    BY ExtraSumRecPrime
  <1> DEFINE P(k) == k \in 0..WN => ExtraSum'[k] = ExtraSum[k]
  <1>1. P(0)  BY <1>rec, <1>recP, WNType
  <1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
    <2> SUFFICES ASSUME k + 1 \in 0..WN PROVE ExtraSum'[k + 1] = ExtraSum[k + 1]
      OBVIOUS
    <2>k. k \in 0..WN  BY WNType
    <2>p. ExtraSum'[k + 1] = ExtraSum'[k] + extra[WEnum[k + 1]]
      BY <2>k, <1>recP
    <2>u. ExtraSum[k + 1] = ExtraSum[k] + extra[WEnum[k + 1]]
      BY <2>k, <1>rec
    <2>ih. ExtraSum'[k] = ExtraSum[k]  BY <2>k, P(k)
    <2> QED  BY <2>p, <2>u, <2>ih
  <1>3. \A k \in Nat : P(k)  BY <1>1, <1>2, NatInduction
  <1> QED  BY <1>3, WNType

\* WSum and ExtraSum fold the same enumeration, one over weights = 1+extra
\* and one over extra: their running totals differ by exactly the running
\* index.  This is the fact that connects Terminal (ExtraSum[WN] = Pool) to
\* Normalization's conclusion (WSum[WN] = WeightTotal).
LEMMA WSumExtraSum ==
  ASSUME extra \in [Candidates -> Nat]
  PROVE  WSum[WN] = ExtraSum[WN] + WN
  <1> USE WNType
  <1>wrec. WSum = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE WSum[i - 1] + weights[WEnum[i]]]
    BY WSumRec
  <1>erec. ExtraSum = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE ExtraSum[i - 1] + extra[WEnum[i]]]
    BY ExtraSumRec
  <1>wnat. weights \in [Candidates -> Nat]  BY DEF weights
  <1>wsnat. \A i \in 0..WN : WSum[i] \in Nat  BY <1>wrec, <1>wnat, FoldType
  <1>ensat. \A i \in 0..WN : ExtraSum[i] \in Nat  BY <1>erec, FoldType
  <1> DEFINE P(k) == k \in 0..WN => WSum[k] = ExtraSum[k] + k
  <1>1. P(0)
    <2> SUFFICES ASSUME 0 \in 0..WN PROVE WSum[0] = ExtraSum[0] + 0  OBVIOUS
    <2> QED  BY <1>wrec, <1>erec
  <1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
    <2> SUFFICES ASSUME k + 1 \in 0..WN PROVE WSum[k + 1] = ExtraSum[k + 1] + (k + 1)  OBVIOUS
    <2>k. k \in 0..WN  OBVIOUS
    <2>e. WEnum[k + 1] \in Candidates  BY WEnumBij
    <2>wval. weights[WEnum[k + 1]] = 1 + extra[WEnum[k + 1]]  BY <2>e DEF weights
    <2>wstep. WSum[k + 1] = WSum[k] + weights[WEnum[k + 1]]  BY <2>k, <1>wrec, FoldRecStep
    <2>estep. ExtraSum[k + 1] = ExtraSum[k] + extra[WEnum[k + 1]]  BY <2>k, <1>erec, FoldRecStep
    <2>ih. WSum[k] = ExtraSum[k] + k  BY <2>k, P(k)
    <2>wk. WSum[k] \in Nat  BY <2>k, <1>wsnat
    <2>ek. ExtraSum[k] \in Nat  BY <2>k, <1>ensat
    <2>ev. extra[WEnum[k + 1]] \in Nat  BY <2>e
    <2> QED  BY <2>wstep, <2>estep, <2>wval, <2>ih, <2>wk, <2>ek, <2>ev
  <1>3. \A k \in Nat : P(k)  BY <1>1, <1>2, NatInduction
  <1>4. P(WN)  BY <1>3
  <1> QED  BY <1>4, WNType

\* Primed counterpart, for the AssignNext step where extra changes.
LEMMA WSumExtraSumPrime ==
  ASSUME extra' \in [Candidates -> Nat]
  PROVE  WSum'[WN] = ExtraSum'[WN] + WN
  <1> USE WNType
  <1>wrec. WSum' = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE WSum'[i - 1] + weights'[WEnum[i]]]
    BY WSumRecPrime
  <1>erec. ExtraSum' = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE ExtraSum'[i - 1] + extra'[WEnum[i]]]
    BY ExtraSumRecPrime
  <1>wnat. weights' \in [Candidates -> Nat]  BY DEF weights
  <1>wsnat. \A i \in 0..WN : WSum'[i] \in Nat  BY <1>wrec, <1>wnat, FoldType
  <1>ensat. \A i \in 0..WN : ExtraSum'[i] \in Nat  BY <1>erec, FoldType
  <1> DEFINE P(k) == k \in 0..WN => WSum'[k] = ExtraSum'[k] + k
  <1>1. P(0)
    <2> SUFFICES ASSUME 0 \in 0..WN PROVE WSum'[0] = ExtraSum'[0] + 0  OBVIOUS
    <2> QED  BY <1>wrec, <1>erec
  <1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
    <2> SUFFICES ASSUME k + 1 \in 0..WN PROVE WSum'[k + 1] = ExtraSum'[k + 1] + (k + 1)  OBVIOUS
    <2>k. k \in 0..WN  OBVIOUS
    <2>e. WEnum[k + 1] \in Candidates  BY WEnumBij
    <2>wval. weights'[WEnum[k + 1]] = 1 + extra'[WEnum[k + 1]]  BY <2>e DEF weights
    <2>wstep. WSum'[k + 1] = WSum'[k] + weights'[WEnum[k + 1]]  BY <2>k, <1>wrec, FoldRecStep
    <2>estep. ExtraSum'[k + 1] = ExtraSum'[k] + extra'[WEnum[k + 1]]  BY <2>k, <1>erec, FoldRecStep
    <2>ih. WSum'[k] = ExtraSum'[k] + k  BY <2>k, P(k)
    <2>wk. WSum'[k] \in Nat  BY <2>k, <1>wsnat
    <2>ek. ExtraSum'[k] \in Nat  BY <2>k, <1>ensat
    <2>ev. extra'[WEnum[k + 1]] \in Nat  BY <2>e
    <2> QED  BY <2>wstep, <2>estep, <2>wval, <2>ih, <2>wk, <2>ek, <2>ev
  <1>3. \A k \in Nat : P(k)  BY <1>1, <1>2, NatInduction
  <1>4. P(WN)  BY <1>3
  <1> QED  BY <1>4, WNType

\* ---- The inductive invariant ---------------------------------------------
\* ScorePositive is an inductive strengthening. It
\* carries the fact that Init's scores \in [Candidates -> 1..MaxScore] (a
\* tighter range than TypeInvariant's 0..MaxScore) survives forever, since
\* scores never changes after Init.  PriorityTie needs scores[c] > 0 to
\* cancel a common factor; without this fact a score of exactly 0 would make
\* every candidate's priority ratio 0 regardless of extra, letting the
\* position tie-break run unchecked.
ScorePositive == \A c \in Candidates : scores[c] > 0

Inv == TypeInvariant /\ NonNegativity /\ BoundedTotal /\ Normalization /\
       UniversalContribution /\ ScoreOrderPreservation /\ TieBoundedness /\
       ScorePositive

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1> USE DEF Init
  <1>ty. TypeInvariant
    <2>1. scores \in [Candidates -> 1..MaxScore]  OBVIOUS
    <2>2. extra \in [Candidates -> Nat]  OBVIOUS
    <2> QED  BY <2>1, <2>2, MaxScoreType DEF TypeInvariant
  <1>sp. ScorePositive  BY DEF ScorePositive
  <1>wc. \A c \in Candidates : weights[c] = 1  BY DEF weights
  <1>wnat. weights \in [Candidates -> Nat]  BY <1>wc DEF weights
  <1>nn. NonNegativity  BY <1>wnat DEF NonNegativity
  <1>uc. UniversalContribution  BY <1>wc DEF UniversalContribution
  <1>sm. ScoreOrderPreservation  BY <1>wc DEF ScoreOrderPreservation
  <1>tb. TieBoundedness  BY <1>wc DEF TieBoundedness
  <1>bt. BoundedTotal
    <2>rec. WSum = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE WSum[i - 1] + weights[WEnum[i]]]
      BY WSumRec
    <2>fold. \A i \in 0..WN : WSum[i] = i
      BY <1>wnat, <1>wc, <2>rec, FoldConstFn
    <2>final. WSum[WN] = WN  BY <2>fold, WNType
    <2>cardbound. Cardinality(Candidates) <= WeightTotal  BY WeightTotalBound
    <2>bound. WN <= WeightTotal  BY <2>cardbound DEF WN
    <2> QED  BY <2>final, <2>bound DEF BoundedTotal
  <1>extranat. extra \in [Candidates -> Nat]  BY <1>ty DEF TypeInvariant
  <1>norm. Normalization
    <2> SUFFICES ASSUME Terminal PROVE WSum[WN] = WeightTotal  BY DEF Normalization
    <2>ext. ExtraSum[WN] = Pool  BY DEF Terminal
    <2>rel. WSum[WN] = ExtraSum[WN] + WN  BY <1>extranat, WSumExtraSum
    <2>arith. Pool + WN = WeightTotal
      BY WeightTotalBound, WeightTotalType, WNType DEF Pool, Reserved
    <2> QED  BY <2>ext, <2>rel, <2>arith
  <1> QED  BY <1>ty, <1>sp, <1>nn, <1>bt, <1>norm, <1>uc, <1>sm, <1>tb DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, NonNegativity, UniversalContribution,
             ScorePositive, weights
  <1>0. CASE UNCHANGED vars
    <2> USE <1>0 DEF vars
    <2>ty. TypeInvariant'  BY DEF TypeInvariant
    <2>sp. ScorePositive'  BY DEF ScorePositive
    <2>nn. NonNegativity'  BY DEF NonNegativity, TypeInvariant, weights
    <2>uc. UniversalContribution'  BY DEF UniversalContribution, TypeInvariant, weights
    <2>sm. ScoreOrderPreservation'  BY DEF ScoreOrderPreservation, weights
    <2>tb. TieBoundedness'  BY DEF TieBoundedness, weights
    \* WSum'[WN] = WSum[WN] and ExtraSum'[WN] = ExtraSum[WN] are shared by
    \* both BoundedTotal' and Normalization' below, so computed once here.
    <2>eeq. extra' = extra  BY DEF vars
    <2>enat. extra \in [Candidates -> Nat]  BY DEF TypeInvariant
    <2>wseq. WSum'[WN] = WSum[WN]  BY <2>enat, <2>eeq, WSumStable
    <2>eseq. ExtraSum'[WN] = ExtraSum[WN]
      BY <2>enat, <2>eeq, ExtraSumStable
    <2>norm. Normalization'
      <3>term. Terminal' <=> Terminal  BY <2>eseq DEF Terminal
      <3>orignorm. Normalization  BY DEF Inv
      <3> QED  BY <3>term, <2>wseq, <3>orignorm DEF Normalization
    <2>bt. BoundedTotal'
      <3>orig. BoundedTotal  BY DEF Inv
      <3> QED  BY <3>orig, <2>wseq DEF BoundedTotal
    <2> QED  BY <2>ty, <2>sp, <2>nn, <2>uc, <2>sm, <2>tb, <2>norm, <2>bt DEF Inv
  <1>1. CASE Next
    <2> USE DEF Next, AssignNext
    <2>guard. WSum[WN] < WeightTotal  BY <1>1
    <2>extraP. extra' = [extra EXCEPT ![Winner] = @ + 1]  BY <1>1
    <2>scoresP. scores' = scores  BY <1>1
    <2>extranat. extra \in [Candidates -> Nat]  BY DEF TypeInvariant
    <2>scoresrange. scores \in [Candidates -> 0..MaxScore]  BY DEF TypeInvariant
    <2>scoresnat. \A c \in Candidates : scores[c] \in Nat
      BY <2>scoresrange, MaxScoreType
    <2>extranat2. \A c \in Candidates : extra[c] \in Nat  BY <2>extranat
    <2>winProp. Winner \in Candidates /\ \A d \in Candidates \ {Winner} : Prefer(Winner, d)
      BY <2>scoresnat, <2>extranat2, WinnerProp
    <2>winC. Winner \in Candidates  BY <2>winProp
    <2>wextra. extra'[Winner] = extra[Winner] + 1
      BY <2>extraP, <2>winC, <2>extranat
    <2>wother. \A c \in Candidates \ {Winner} : extra'[c] = extra[c]
      BY <2>extraP, <2>winC
    <2>extra2. extra' \in [Candidates -> Nat]
      <3> SUFFICES ASSUME NEW c \in Candidates PROVE extra'[c] \in Nat
        BY <2>extraP, <2>extranat
      <3>A. CASE c = Winner  BY <3>A, <2>wextra, <2>extranat2, <2>winC
      <3>B. CASE c # Winner  BY <3>B, <2>wother, <2>extranat2
      <3> QED  BY <3>A, <3>B
    <2>ty. TypeInvariant'
      <3>1. scores' \in [Candidates -> 0..MaxScore]  BY <2>scoresP, <2>scoresrange
      <3> QED  BY <3>1, <2>extra2 DEF TypeInvariant
    <2>weightsP. \A c \in Candidates :
                   weights'[c] = IF c = Winner THEN weights[c] + 1 ELSE weights[c]
      <3> SUFFICES ASSUME NEW c \in Candidates
                   PROVE weights'[c] = IF c = Winner THEN weights[c] + 1 ELSE weights[c]
        OBVIOUS
      <3>A. CASE c = Winner
        <4>1. weights'[c] = 1 + extra'[c]  BY DEF weights
        <4>2. extra'[c] = extra[Winner] + 1  BY <3>A, <2>wextra
        <4>3. weights[c] = 1 + extra[c]  BY DEF weights
        <4> QED  BY <4>1, <4>2, <4>3, <3>A
      <3>B. CASE c # Winner
        <4>1. weights'[c] = 1 + extra'[c]  BY DEF weights
        <4>2. extra'[c] = extra[c]  BY <3>B, <2>wother
        <4>3. weights[c] = 1 + extra[c]  BY DEF weights
        <4>4. weights'[c] = weights[c]  BY <4>1, <4>2, <4>3
        <4> QED  BY <4>4, <3>B
      <3> QED  BY <3>A, <3>B
    \* BoundedTotal follows from the single-winner fold delta and the guard.
    <2>bt. BoundedTotal'
      <3>wspec. weights' = [weights EXCEPT ![Winner] = weights[Winner] + 1]
        <4> SUFFICES ASSUME NEW c \in Candidates
                     PROVE weights'[c] = [weights EXCEPT ![Winner] = weights[Winner] + 1][c]
          BY DEF weights
        <4>A. CASE c = Winner
          <5>1. weights'[c] = weights[c] + 1  BY <4>A, <2>weightsP
          <5> QED  BY <5>1, <4>A
        <4>B. CASE c # Winner
          <5>1. weights'[c] = weights[c]  BY <4>B, <2>weightsP
          <5> QED  BY <5>1, <4>B
        <4> QED  BY <4>A, <4>B
      <3>gnat. weights \in [Candidates -> Nat]  BY DEF TypeInvariant, weights
      <3>hnat. weights' \in [Candidates -> Nat]  BY <2>ty DEF TypeInvariant, weights
      <3>rec. WSum = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE WSum[i - 1] + weights[WEnum[i]]]
        BY WSumRec
      <3>recP. WSum' = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE WSum'[i - 1] + weights'[WEnum[i]]]
        BY WSumRecPrime
      \* AssignNext's EXCEPT touches only Winner, so the fold changes by
      \* exactly 1: a single-name delta induction over the enumeration.
      \* The derived recursion equations relate the current and primed folds.
      <3>delta. WSum'[WN] = WSum[WN] + 1
        <4> DEFINE Seen1(k) == \E j \in 1..k : WEnum[j] = Winner
        <4> DEFINE P(k) == k \in 0..WN => WSum'[k] = WSum[k] + (IF Seen1(k) THEN 1 ELSE 0)
        <4>gN. \A i \in 0..WN : WSum[i] \in Nat  BY <3>gnat, <3>rec, FoldType
        <4>1. P(0)
          <5> SUFFICES ASSUME 0 \in 0..WN
                       PROVE  WSum'[0] = WSum[0] + (IF Seen1(0) THEN 1 ELSE 0)
            OBVIOUS
          <5>1. WSum'[0] = 0 /\ WSum[0] = 0  BY <3>rec, <3>recP
          <5>2. ~ Seen1(0)  OBVIOUS
          <5> QED  BY <5>1, <5>2
        <4>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
          <5> SUFFICES ASSUME k + 1 \in 0..WN
                       PROVE  WSum'[k + 1] = WSum[k + 1] + (IF Seen1(k + 1) THEN 1 ELSE 0)
            OBVIOUS
          <5>k. k \in 0..WN  BY WNType
          <5>kp1. k + 1 \in 0..WN  OBVIOUS
          <5>kp1dom. k + 1 \in 1..WN  BY <5>kp1
          <5>enumtype. WEnum \in [1..WN -> Candidates]  BY WEnumBij
          <5>e. WEnum[k + 1] \in Candidates  BY <5>kp1dom, <5>enumtype
          <5>gk. WSum[k] \in Nat  BY <5>k, <4>gN
          <5>gN1. weights[WEnum[k + 1]] \in Nat  BY <5>e, <3>gnat
          <5>Geq. WSum[k + 1] = WSum[k] + weights[WEnum[k + 1]]
            BY <5>kp1, <3>rec, FoldRecStep
          <5>Heq. WSum'[k + 1] = WSum'[k] + weights'[WEnum[k + 1]]
            BY <5>kp1, <3>recP, FoldRecStep
          <5>hval. weights'[WEnum[k + 1]] = IF WEnum[k + 1] = Winner THEN weights[Winner] + 1
                                             ELSE weights[WEnum[k + 1]]
            BY <5>e, <3>wspec
          <5>ih. WSum'[k] = WSum[k] + (IF Seen1(k) THEN 1 ELSE 0)  BY <5>k, P(k)
          <5>A. CASE WEnum[k + 1] = Winner
            <6>ns1. ~ Seen1(k)
              <7> SUFFICES ASSUME NEW j \in 1..k, WEnum[j] = Winner PROVE FALSE  OBVIOUS
              <7>1. j \in 1..WN /\ (k + 1) \in 1..WN  BY WNType
              <7>2. WEnum[j] = WEnum[k + 1]  BY <5>A
              <7>3. j = k + 1  BY <7>1, <7>2, WEnumBij
              <7> QED  BY <7>3
            <6>s1. Seen1(k + 1)  BY <5>A
            <6>hv. weights'[WEnum[k + 1]] = weights[Winner] + 1  BY <5>hval, <5>A
            <6>gv. weights[WEnum[k + 1]] = weights[Winner]  BY <5>A
            <6> QED
              BY <5>Heq, <5>Geq, <5>ih, <6>hv, <6>gv, <6>ns1, <6>s1, <5>gk, <5>gN1
          <5>B. CASE WEnum[k + 1] # Winner
            <6>hv. weights'[WEnum[k + 1]] = weights[WEnum[k + 1]]  BY <5>hval, <5>B
            <6>s1eq. Seen1(k + 1) <=> Seen1(k)  BY <5>B
            <6> QED
              BY <5>Heq, <5>Geq, <5>ih, <6>hv, <6>s1eq, <5>gk, <5>gN1
          <5> QED  BY <5>A, <5>B
        <4>3. \A k \in Nat : P(k)  BY <4>1, <4>2, NatInduction
        <4>4. P(WN)  BY <4>3
        <4>wnrange. WN \in 0..WN  BY WNType
        <4>s1. Seen1(WN)  BY <2>winC, WEnumBij
        <4> QED  BY <4>4, <4>wnrange, <4>s1
      <3>wsumnatall. \A i \in 0..WN : WSum[i] \in Nat  BY <3>gnat, <3>rec, FoldType
      <3>wsumnat. WSum[WN] \in Nat  BY <3>wsumnatall, WNType
      <3>1. WSum'[WN] <= WeightTotal  BY <3>delta, <2>guard, <3>wsumnat, WeightTotalType
      <3> QED  BY <3>1 DEF BoundedTotal
    <2>sp. ScorePositive'  BY <2>scoresP DEF ScorePositive
    <2>nn. NonNegativity'  BY <2>ty DEF NonNegativity, TypeInvariant, weights
    <2>uc. UniversalContribution'  BY <2>ty DEF UniversalContribution, TypeInvariant, weights
    <2>norm. Normalization'
      <3> SUFFICES ASSUME Terminal' PROVE WSum'[WN] = WeightTotal  BY DEF Normalization
      <3>ext. ExtraSum'[WN] = Pool  BY DEF Terminal
      <3>rel. WSum'[WN] = ExtraSum'[WN] + WN  BY <2>extra2, WSumExtraSumPrime
      <3>arith. Pool + WN = WeightTotal
        BY WeightTotalBound, WeightTotalType, WNType DEF Pool, Reserved
      <3> QED  BY <3>ext, <3>rel, <3>arith
    <2>sm. ScoreOrderPreservation'
      <3> SUFFICES ASSUME NEW c \in Candidates, NEW d \in Candidates, scores'[c] < scores'[d]
                   PROVE weights'[c] <= weights'[d]
        BY DEF ScoreOrderPreservation
      <3>sc. scores[c] < scores[d]  BY <2>scoresP
      <3>ih. weights[c] <= weights[d]  BY <3>sc DEF ScoreOrderPreservation
      <3>A. CASE c = Winner /\ d = Winner  BY <3>A, <3>sc
      <3>B. CASE c = Winner /\ d # Winner
        <4>wc. weights'[c] = weights[c] + 1  BY <3>B, <2>weightsP
        <4>wd. weights'[d] = weights[d]  BY <3>B, <2>weightsP
        <4>dnotc. d \in Candidates \ {Winner}  BY <3>B
        <4>pref. Prefer(Winner, d)  BY <2>winProp, <4>dnotc
        <4>strict. extra[c] < extra[d]
          BY <3>B, <4>pref, <3>sc, <2>scoresnat, <2>extranat2, PriorityStrict
        <4>wless. weights[c] < weights[d]  BY <4>strict DEF weights
        <4> QED  BY <4>wc, <4>wd, <4>wless
      <3>C. CASE c # Winner /\ d = Winner
        <4>wc. weights'[c] = weights[c]  BY <3>C, <2>weightsP
        <4>wd. weights'[d] = weights[d] + 1  BY <3>C, <2>weightsP
        <4> QED  BY <3>ih, <4>wc, <4>wd
      <3>D. CASE c # Winner /\ d # Winner
        <4>wc. weights'[c] = weights[c]  BY <3>D, <2>weightsP
        <4>wd. weights'[d] = weights[d]  BY <3>D, <2>weightsP
        <4> QED  BY <3>ih, <4>wc, <4>wd
      <3> QED  BY <3>A, <3>B, <3>C, <3>D
    <2>tb. TieBoundedness'
      <3> SUFFICES ASSUME NEW c \in Candidates, NEW d \in Candidates, scores'[c] = scores'[d]
                   PROVE weights'[c] <= weights'[d] + 1 /\ weights'[d] <= weights'[c] + 1
        BY DEF TieBoundedness
      <3>sc. scores[c] = scores[d]  BY <2>scoresP
      <3>ihcd. weights[c] <= weights[d] + 1  BY <3>sc DEF TieBoundedness
      <3>ihdc. weights[d] <= weights[c] + 1  BY <3>sc DEF TieBoundedness
      <3>scpos. scores[c] > 0  BY DEF ScorePositive
      <3>A. CASE c = Winner /\ d = Winner
        <4>wc. weights'[c] = weights[c] + 1  BY <3>A, <2>weightsP
        <4>wd. weights'[d] = weights[d] + 1  BY <3>A, <2>weightsP
        <4>cd. c = d  BY <3>A
        <4> QED  BY <4>wc, <4>wd, <4>cd
      <3>B. CASE c = Winner /\ d # Winner
        <4>wc. weights'[c] = weights[c] + 1  BY <3>B, <2>weightsP
        <4>wd. weights'[d] = weights[d]  BY <3>B, <2>weightsP
        <4>dnotc. d \in Candidates \ {Winner}  BY <3>B
        <4>pref. Prefer(Winner, d)  BY <2>winProp, <4>dnotc
        <4>tie. extra[c] <= extra[d]
          BY <3>B, <4>pref, <3>sc, <3>scpos, <2>scoresnat, <2>extranat2, PriorityTie
        <4>wle. weights[c] <= weights[d]  BY <4>tie DEF weights
        <4>dir1. weights'[c] <= weights'[d] + 1  BY <4>wc, <4>wd, <4>wle
        <4>dir2. weights'[d] <= weights'[c] + 1  BY <4>wc, <4>wd, <3>ihdc
        <4> QED  BY <4>dir1, <4>dir2
      <3>C. CASE c # Winner /\ d = Winner
        <4>wc. weights'[c] = weights[c]  BY <3>C, <2>weightsP
        <4>wd. weights'[d] = weights[d] + 1  BY <3>C, <2>weightsP
        <4>cnotd. c \in Candidates \ {Winner}  BY <3>C
        <4>pref. Prefer(Winner, c)  BY <2>winProp, <4>cnotd
        <4>scsym. scores[d] = scores[c]  BY <3>sc
        <4>scpos2. scores[d] > 0  BY <3>scpos, <3>sc
        <4>tie. extra[d] <= extra[c]
          BY <3>C, <4>pref, <4>scsym, <4>scpos2, <2>scoresnat, <2>extranat2, PriorityTie
        <4>wle. weights[d] <= weights[c]  BY <4>tie DEF weights
        <4>dir1. weights'[c] <= weights'[d] + 1  BY <4>wc, <4>wd, <3>ihcd
        <4>dir2. weights'[d] <= weights'[c] + 1  BY <4>wc, <4>wd, <4>wle
        <4> QED  BY <4>dir1, <4>dir2
      <3>D. CASE c # Winner /\ d # Winner
        <4>wc. weights'[c] = weights[c]  BY <3>D, <2>weightsP
        <4>wd. weights'[d] = weights[d]  BY <3>D, <2>weightsP
        <4> QED  BY <3>ihcd, <3>ihdc, <4>wc, <4>wd
      <3> QED  BY <3>A, <3>B, <3>C, <3>D
    <2> QED  BY <2>ty, <2>sp, <2>nn, <2>uc, <2>norm, <2>sm, <2>tb, <2>bt DEF Inv
  <1> QED  BY <1>0, <1>1

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                  BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'   BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant  BY Safety, PTL DEF Inv
THEOREM NonNegativitySafety == Spec => []NonNegativity  BY Safety, PTL DEF Inv
THEOREM BoundedTotalSafety == Spec => []BoundedTotal  BY Safety, PTL DEF Inv
THEOREM NormalizationSafety == Spec => []Normalization  BY Safety, PTL DEF Inv
THEOREM UniversalContributionSafety == Spec => []UniversalContribution  BY Safety, PTL DEF Inv
THEOREM ScoreOrderPreservationSafety == Spec => []ScoreOrderPreservation  BY Safety, PTL DEF Inv
THEOREM TieBoundednessSafety == Spec => []TieBoundedness  BY Safety, PTL DEF Inv
====
