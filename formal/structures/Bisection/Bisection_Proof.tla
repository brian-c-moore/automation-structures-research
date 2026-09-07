---- MODULE Bisection_Proof ----
(* Proof of Bisection's public invariants TypeInvariant,
   MonotonicityPreservation, and ProbeBound, plus Halving and
   EventualConvergence.

   ProbeBound (probes_taken <= MaxProbes) is not inductive on its own: from
   probes_taken = MaxProbes a probe would give MaxProbes + 1.  The inductive
   certificate is the exponential strengthening

       WidthExpBound == hi - lo <= Pow2[MaxProbes - probes_taken]

   where Pow2 is the powers-of-two function.  When a probe is enabled
   (hi - lo >= 2), WidthExpBound forces MaxProbes - probes_taken >= 1, i.e.
   probes_taken < MaxProbes; and the halving (hi' - lo' <= (hi - lo) \div 2)
   re-establishes the bound with the exponent decremented.  Pow2 facts come
   from the NaturalsInduction library; the halving uses integer-division
   lemmas.  Every reindexing of Pow2 (Pow2[a] = Pow2[b] from a = b) is an
   explicit congruence step, and every Pow2[..] and \div term carries its
   `\in Nat` typing in the BY so the `<=` chains propagate arithmetically. *)
EXTENDS Bisection, Naturals, NaturalsInduction, TLAPS

\* ---- Constant typing + the model's domain-fits-probes relationship --------
\* DomainSizeType, MaxProbesType, ThresholdType and DomainFitsProbes are
\* Bisection's own constant assumptions and arrive by EXTENDS, together with
\* the Pow2 function DomainFitsProbes is stated over. They belong to the
\* specification: carried here alone they would bound what this proof
\* establishes while leaving the module satisfiable at constants that falsify
\* ProbeBound.
\*
\* ---- Pow2 facts -----------------------------------------------------------
\* Pow2 is a recursive definition, so DEF Pow2 does not expand it.  The
\* recursion equation and the Nat type come from the NaturalsInduction
\* library, instantiated at f0 = 1 and Def(v, n) = 2 * v; the facts the proof
\* uses are derived from those.
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

\* For k >= 1, Pow2[k] = 2 * Pow2[k-1], hence Pow2[k] \div 2 = Pow2[k-1].
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

\* ---- Integer-division facts ----------------------------------------------

LEMMA DivHalfMono ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a <= b
  PROVE  a \div 2 <= b \div 2
  OBVIOUS

\* Midpoint facts under a <= b: the midpoint is a well-typed interior point,
\* and (a+b)\div2 - a collapses to the half-width (b-a)\div2.
LEMMA MidFacts ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a <= b
  PROVE  /\ (a + b) \div 2 \in Nat
         /\ a <= (a + b) \div 2
         /\ (a + b) \div 2 <= b
         /\ (a + b) \div 2 - a = (b - a) \div 2
  OBVIOUS

\* Strict midpoint facts when the interval is non-trivial (b - a >= 2):
\* the midpoint is strictly below b, and the right sub-interval's width
\* b - (Mid + 1) is at most the half-width.
LEMMA MidStrictFacts ==
  ASSUME NEW a \in Nat, NEW b \in Nat, b - a >= 2
  PROVE  /\ (a + b) \div 2 <= b - 1
         /\ b - ((a + b) \div 2 + 1) <= (b - a) \div 2
  OBVIOUS

\* x \div 2 is a Nat no larger than x (interval never grows under a probe).
LEMMA DivHalfLeSelf ==
  ASSUME NEW x \in Nat
  PROVE  x \div 2 \in Nat /\ x \div 2 <= x
  OBVIOUS

\* ---- Inductive invariant --------------------------------------------------
\* WidthExpBound is an inductive strengthening used to prove ProbeBound.

WidthExpBound == hi - lo <= Pow2[MaxProbes - probes_taken]

Inv ==
  /\ TypeInvariant
  /\ MonotonicityPreservation
  /\ ProbeBound
  /\ WidthExpBound

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1> USE DEF Init
  <1>1. TypeInvariant
    BY DomainSizeType, ThresholdType DEF TypeInvariant
  <1>2. MonotonicityPreservation
    BY DEF MonotonicityPreservation
  <1>3. ProbeBound
    BY MaxProbesType DEF ProbeBound
  <1>4. WidthExpBound
    <2>0. probes_taken = 0
      BY DEF Init
    <2>1. MaxProbes - probes_taken = MaxProbes
      BY <2>0, MaxProbesType
    <2>1a. Pow2[MaxProbes - probes_taken] \in Nat
      BY <2>0, MaxProbesType, Pow2Val
    <2>2. hi - lo <= DomainSize
      BY <1>1, DomainSizeType DEF TypeInvariant
    <2>3. Pow2[MaxProbes - probes_taken] = Pow2[MaxProbes]
      BY <2>1
    <2>4. DomainSize <= Pow2[MaxProbes - probes_taken]
      BY <2>3, <2>1a, DomainFitsProbes, DomainSizeType
    <2>5. hi - lo <= Pow2[MaxProbes - probes_taken]
      BY <2>2, <2>4, <2>1a, DomainSizeType
    <2> QED  BY <2>5 DEF WidthExpBound
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, MonotonicityPreservation,
              ProbeBound, WidthExpBound
  \* Common unprimed-state facts available in every case.
  <1>nat. /\ lo \in Nat
          /\ hi \in Nat
          /\ probes_taken \in Nat
          /\ lo <= hi
          /\ MaxProbes - probes_taken \in Nat
    BY DomainSizeType, MaxProbesType, ThresholdType
  <1>p2. Pow2[MaxProbes - probes_taken] \in Nat
    BY <1>nat, Pow2Val
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE ProbeLeft
    <2> USE <1>1 DEF ProbeLeft
    <2>g.  hi - lo >= 2                 OBVIOUS
    <2>m.  Mid >= Threshold             OBVIOUS
    <2>hp. hi' = Mid                    OBVIOUS
    <2>lp. lo' = lo                     OBVIOUS
    <2>pp. probes_taken' = probes_taken + 1   OBVIOUS
    \* Midpoint facts (Mid = (lo+hi)\div2).
    <2>mid. /\ Mid \in Nat
            /\ lo <= Mid
            /\ Mid <= hi
            /\ Mid - lo = (hi - lo) \div 2
      BY <1>nat, MidFacts DEF Mid
    <2>w. /\ (hi - lo) \in Nat
          /\ (hi - lo) \div 2 \in Nat
          /\ (hi - lo) \div 2 <= hi - lo
      BY <1>nat, DivHalfLeSelf
    \* TypeInvariant'
    <2>1. TypeInvariant'
      <3>1. lo' \in 0..DomainSize       BY <2>lp
      <3>2. hi' \in 0..DomainSize       BY <2>hp, <2>mid, DomainSizeType
      <3>3. probes_taken' \in Nat       BY <2>pp, <1>nat
      <3> QED  BY <3>1, <3>2, <3>3 DEF TypeInvariant
    \* MonotonicityPreservation': lo'=lo<=Threshold; Threshold<=hi'=Mid (guard).
    <2>3. MonotonicityPreservation'
      BY <2>lp, <2>hp, <2>m DEF MonotonicityPreservation
    \* ProbeBound': probes_taken + 1 <= MaxProbes, via WidthExpBound + guard.
    <2>term. probes_taken + 1 <= MaxProbes
      <3>1. CASE probes_taken = MaxProbes
        <4>1. MaxProbes - probes_taken = 0            BY <3>1, MaxProbesType
        <4>2. Pow2[MaxProbes - probes_taken] = Pow2[0]   BY <4>1
        <4>3. Pow2[MaxProbes - probes_taken] = 1      BY <4>2, Pow2Zero
        <4>4. hi - lo <= 1                            BY <4>3
        <4> QED  BY <4>4, <2>g, <1>nat
      <3>2. CASE probes_taken # MaxProbes
        BY <3>2, <1>nat, MaxProbesType
      <3> QED  BY <3>1, <3>2
    <2>4. ProbeBound'
      BY <2>pp, <2>term DEF ProbeBound
    \* WidthExpBound': hi' - lo' = (hi-lo)\div2 <= Pow2[k]\div2 = Pow2[k-1].
    <2>5. WidthExpBound'
      <3>k1. MaxProbes - probes_taken >= 1
        BY <2>term, <1>nat, MaxProbesType
      <3>pk. /\ Pow2[MaxProbes - probes_taken] \div 2 \in Nat
             /\ Pow2[(MaxProbes - probes_taken) - 1] \in Nat
        <4>1. (MaxProbes - probes_taken) - 1 \in Nat   BY <3>k1, <1>nat
        <4> QED  BY <1>p2, <4>1, DivHalfLeSelf, Pow2Val
      <3>1. hi' - lo' = (hi - lo) \div 2
        BY <2>hp, <2>lp, <2>mid
      <3>2. hi - lo <= Pow2[MaxProbes - probes_taken]
        BY DEF WidthExpBound
      <3>4. (hi - lo) \div 2 <= Pow2[MaxProbes - probes_taken] \div 2
        BY <3>2, <1>p2, <2>w, DivHalfMono
      <3>5. Pow2[MaxProbes - probes_taken] \div 2 = Pow2[(MaxProbes - probes_taken) - 1]
        BY <1>nat, <3>k1, Pow2HalfStep
      <3>6. Pow2[(MaxProbes - probes_taken) - 1] = Pow2[MaxProbes - probes_taken']
        <4>1. (MaxProbes - probes_taken) - 1 = MaxProbes - probes_taken'
          BY <2>pp, <1>nat, MaxProbesType
        <4> QED  BY <4>1
      <3>7. hi' - lo' <= Pow2[MaxProbes - probes_taken']
        BY <3>1, <3>4, <3>5, <3>6, <2>w, <3>pk
      <3> QED  BY <3>7 DEF WidthExpBound
    <2> QED  BY <2>1, <2>3, <2>4, <2>5 DEF Inv
  <1>2. CASE ProbeRight
    <2> USE <1>2 DEF ProbeRight
    <2>g.  hi - lo >= 2                 OBVIOUS
    <2>m.  Mid < Threshold             OBVIOUS
    <2>hp. hi' = hi                    OBVIOUS
    <2>lp. lo' = Mid + 1               OBVIOUS
    <2>pp. probes_taken' = probes_taken + 1   OBVIOUS
    <2>mid. /\ Mid \in Nat
            /\ lo <= Mid
            /\ Mid <= hi
            /\ Mid - lo = (hi - lo) \div 2
      BY <1>nat, MidFacts DEF Mid
    <2>mids. /\ Mid <= hi - 1
             /\ hi - (Mid + 1) <= (hi - lo) \div 2
      BY <1>nat, <2>g, MidStrictFacts DEF Mid
    <2>w. /\ (hi - lo) \in Nat
          /\ (hi - lo) \div 2 \in Nat
          /\ (hi - lo) \div 2 <= hi - lo
      BY <1>nat, DivHalfLeSelf
    \* TypeInvariant': lo' = Mid+1 \in 0..DomainSize (Mid+1 <= hi <= DomainSize).
    <2>1. TypeInvariant'
      <3>1. hi' \in 0..DomainSize       BY <2>hp
      <3>2. lo' \in 0..DomainSize       BY <2>lp, <2>mid, <2>mids, DomainSizeType
      <3>3. probes_taken' \in Nat       BY <2>pp, <1>nat
      <3> QED  BY <3>1, <3>2, <3>3 DEF TypeInvariant
    \* MonotonicityPreservation': lo'=Mid+1<=Threshold (Mid<Threshold); Threshold<=hi'=hi.
    <2>3. MonotonicityPreservation'
      BY <2>lp, <2>hp, <2>m, <2>mid, ThresholdType DEF MonotonicityPreservation
    <2>term. probes_taken + 1 <= MaxProbes
      <3>1. CASE probes_taken = MaxProbes
        <4>1. MaxProbes - probes_taken = 0            BY <3>1, MaxProbesType
        <4>2. Pow2[MaxProbes - probes_taken] = Pow2[0]   BY <4>1
        <4>3. Pow2[MaxProbes - probes_taken] = 1      BY <4>2, Pow2Zero
        <4>4. hi - lo <= 1                            BY <4>3
        <4> QED  BY <4>4, <2>g, <1>nat
      <3>2. CASE probes_taken # MaxProbes
        BY <3>2, <1>nat, MaxProbesType
      <3> QED  BY <3>1, <3>2
    <2>4. ProbeBound'
      BY <2>pp, <2>term DEF ProbeBound
    <2>5. WidthExpBound'
      <3>k1. MaxProbes - probes_taken >= 1
        BY <2>term, <1>nat, MaxProbesType
      <3>pk. /\ Pow2[MaxProbes - probes_taken] \div 2 \in Nat
             /\ Pow2[(MaxProbes - probes_taken) - 1] \in Nat
        <4>1. (MaxProbes - probes_taken) - 1 \in Nat   BY <3>k1, <1>nat
        <4> QED  BY <1>p2, <4>1, DivHalfLeSelf, Pow2Val
      <3>1. hi' - lo' <= (hi - lo) \div 2
        <4>1. hi' - lo' = hi - (Mid + 1)  BY <2>hp, <2>lp
        <4> QED  BY <4>1, <2>mids
      <3>2. hi - lo <= Pow2[MaxProbes - probes_taken]
        BY DEF WidthExpBound
      <3>4. (hi - lo) \div 2 <= Pow2[MaxProbes - probes_taken] \div 2
        BY <3>2, <1>p2, <2>w, DivHalfMono
      <3>5. Pow2[MaxProbes - probes_taken] \div 2 = Pow2[(MaxProbes - probes_taken) - 1]
        BY <1>nat, <3>k1, Pow2HalfStep
      <3>6. Pow2[(MaxProbes - probes_taken) - 1] = Pow2[MaxProbes - probes_taken']
        <4>1. (MaxProbes - probes_taken) - 1 = MaxProbes - probes_taken'
          BY <2>pp, <1>nat, MaxProbesType
        <4> QED  BY <4>1
      <3>7. hi' - lo' <= Pow2[MaxProbes - probes_taken']
        BY <3>1, <3>4, <3>5, <3>6, <2>w, <3>pk
      <3> QED  BY <3>7 DEF WidthExpBound
    <2> QED  BY <2>1, <2>3, <2>4, <2>5 DEF Inv
  <1>3. CASE Converged
    BY <1>3 DEF Converged, vars
  <1>X. CASE Next
    BY <1>X, <1>1, <1>2, <1>3 DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                  BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'   BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

\* Corollaries in the carrier's public invariant vocabulary.
THEOREM TypeSafety == Spec => []TypeInvariant                       BY Safety, PTL DEF Inv
THEOREM MonotonicityPreservationSafety == Spec => []MonotonicityPreservation  BY Safety, PTL DEF Inv
THEOREM ProbeBoundSafety == Spec => []ProbeBound                    BY Safety, PTL DEF Inv

\* ---- Per-probe contraction ------------------------------------------------
\* Halving is the action property [][ContractionStep]_vars, not a state
\* invariant. ContractionLemma is the one-step fact; HalvingProperty lifts it
\* to the temporal action property.
LEMMA ContractionLemma == Inv /\ [Next]_vars => ContractionStep
  <1> SUFFICES ASSUME Inv, [Next]_vars, probes_taken' > probes_taken
               PROVE  hi' - lo' <= (hi - lo) \div 2
    BY DEF ContractionStep
  <1> USE DEF Inv, TypeInvariant, MonotonicityPreservation, ProbeBound
  <1>nat. /\ lo \in Nat /\ hi \in Nat /\ probes_taken \in Nat /\ lo <= hi
    BY DomainSizeType, ThresholdType
  <1>0. CASE UNCHANGED vars
    BY <1>0, <1>nat DEF vars
  <1>1. CASE ProbeLeft
    <2> USE <1>1 DEF ProbeLeft
    <2>mid. /\ Mid \in Nat /\ lo <= Mid /\ Mid <= hi
            /\ Mid - lo = (hi - lo) \div 2
      BY <1>nat, MidFacts DEF Mid
    <2> QED  BY <2>mid
  <1>2. CASE ProbeRight
    <2> USE <1>2 DEF ProbeRight
    <2>g.  hi - lo >= 2                  OBVIOUS
    <2>mids. hi - (Mid + 1) <= (hi - lo) \div 2
      BY <1>nat, <2>g, MidStrictFacts DEF Mid
    <2> QED  BY <2>mids
  <1>3. CASE Converged
    BY <1>3, <1>nat DEF Converged, vars
  <1>X. CASE Next
    BY <1>X, <1>1, <1>2, <1>3 DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM HalvingProperty == Spec => Halving
  <1>1. Inv /\ [Next]_vars => [ContractionStep]_vars
    BY ContractionLemma
  <1>2. Spec => []Inv  BY Safety
  <1> QED  BY <1>1, <1>2, PTL DEF Spec, Halving

\* ---- Eventual convergence --------------------------------------------------
\* Liveness: under WF_vars(ProbeLeft \/ ProbeRight), the interval eventually
\* narrows to a point.  The proof is a downward induction on
\* Remaining == MaxProbes - probes_taken, a Nat that decrements by exactly one
\* on every probe by WidthExpBound and ProbeBound. P(m) carries the goal
\* itself as a standing disjunct (hi - lo < 2 \/ Remaining = m) rather than
\* Remaining = m alone, because Remaining can freeze above zero once
\* hi - lo < 2 is reached early: the DomainFitsProbes bound is <=, not =, so
\* convergence need not exhaust the full probe budget.
THEOREM EventualConvergenceProved == Spec => EventualConvergence
PROOF
  <1> DEFINE P(m) == Spec => <>(hi - lo < 2 \/ MaxProbes - probes_taken = m)
  <1> HIDE DEF P
  <1>base. P(MaxProbes)
    <2> SUFFICES ASSUME Spec
                 PROVE  <>(hi - lo < 2 \/ MaxProbes - probes_taken = MaxProbes)
      BY DEF P
    <2>1. Init => (MaxProbes - probes_taken = MaxProbes)
      BY MaxProbesType DEF Init
    <2> QED  BY <2>1, PTL DEF Spec
  <1>step. \A n \in 1 .. MaxProbes : P(n) => P(n - 1)
    <2> SUFFICES ASSUME NEW n \in 1 .. MaxProbes
                 PROVE  Spec /\ <>(hi - lo < 2 \/ MaxProbes - probes_taken = n)
                          => <>(hi - lo < 2 \/ MaxProbes - probes_taken = (n - 1))
      BY DEF P
    <2>i. Inv /\ (hi - lo < 2 \/ MaxProbes - probes_taken = n) /\ [Next]_vars
            => \/ (hi - lo < 2)'
               \/ (MaxProbes - probes_taken = n)'
               \/ (MaxProbes - probes_taken = (n - 1))'
      <3> SUFFICES ASSUME Inv, (hi - lo < 2 \/ MaxProbes - probes_taken = n),
                          [Next]_vars
                   PROVE  \/ (hi - lo < 2)'
                          \/ (MaxProbes - probes_taken = n)'
                          \/ (MaxProbes - probes_taken = (n - 1))'
        OBVIOUS
      <3> USE DEF Inv, TypeInvariant
      <3>nat. lo \in Nat /\ hi \in Nat /\ probes_taken \in Nat
        BY DomainSizeType
      <3>0. CASE UNCHANGED vars
        BY <3>0 DEF vars
      <3>1. CASE ProbeLeft
        BY <3>1, <3>nat, MaxProbesType DEF ProbeLeft
      <3>2. CASE ProbeRight
        BY <3>2, <3>nat, MaxProbesType DEF ProbeRight
      <3>3. CASE Converged
        BY <3>3 DEF Converged, vars
      <3>X. CASE Next
        BY <3>X, <3>1, <3>2, <3>3 DEF Next
      <3> QED  BY <3>0, <3>X
    <2>ii. Inv /\ (hi - lo < 2 \/ MaxProbes - probes_taken = n)
             /\ <<Next>>_vars /\ (ProbeLeft \/ ProbeRight)
             => (hi - lo < 2)' \/ (MaxProbes - probes_taken = (n - 1))'
      <3> SUFFICES ASSUME Inv, (hi - lo < 2 \/ MaxProbes - probes_taken = n),
                          <<Next>>_vars, (ProbeLeft \/ ProbeRight)
                   PROVE  (hi - lo < 2)' \/ (MaxProbes - probes_taken = (n - 1))'
        OBVIOUS
      <3> USE DEF Inv, TypeInvariant
      <3>nat. lo \in Nat /\ hi \in Nat /\ probes_taken \in Nat
        BY DomainSizeType
      <3>1. CASE ProbeLeft
        BY <3>1, <3>nat, MaxProbesType DEF ProbeLeft
      <3>2. CASE ProbeRight
        BY <3>2, <3>nat, MaxProbesType DEF ProbeRight
      <3> QED  BY <3>1, <3>2
    <2>iii. Inv /\ (hi - lo < 2 \/ MaxProbes - probes_taken = n) /\ ~(hi - lo < 2)
              => ENABLED <<ProbeLeft \/ ProbeRight>>_vars
      <3> SUFFICES ASSUME Inv, hi - lo >= 2
                   PROVE  ENABLED <<ProbeLeft \/ ProbeRight>>_vars
        BY DomainSizeType DEF Inv, TypeInvariant, ProbeLeft, ProbeRight
      <3>nat. /\ lo \in Nat /\ hi \in Nat /\ lo <= hi
              /\ Mid \in Nat /\ lo <= Mid /\ Mid <= hi
        BY DomainSizeType, ThresholdType DEF Inv, TypeInvariant,
                                              MonotonicityPreservation, Mid
      \* ENABLED does not distribute over \/ automatically: first replace the
      \* disjunction's <<.>>_vars form with a disjunction of already-decorated
      \* actions (ENABLEDrules), then distribute ENABLED over that bare \/
      \* (ENABLEDaxioms).
      <3>eq. <<ProbeLeft \/ ProbeRight>>_vars <=> <<ProbeLeft>>_vars \/ <<ProbeRight>>_vars
        BY DEF vars
      <3>dist. ENABLED <<ProbeLeft \/ ProbeRight>>_vars
                 <=> ENABLED <<ProbeLeft>>_vars \/ ENABLED <<ProbeRight>>_vars
        <4>1. ENABLED <<ProbeLeft \/ ProbeRight>>_vars
                <=> ENABLED (<<ProbeLeft>>_vars \/ <<ProbeRight>>_vars)
          BY <3>eq, ENABLEDrules
        <4>2. ENABLED (<<ProbeLeft>>_vars \/ <<ProbeRight>>_vars)
                <=> ENABLED <<ProbeLeft>>_vars \/ ENABLED <<ProbeRight>>_vars
          BY ENABLEDaxioms
        <4> QED  BY <4>1, <4>2
      \* Each case targets only its own single action's ENABLED, so the other
      \* disjunct's operator never appears and no hidden-definition complaint
      \* arises, then lifts to the disjunctive goal via <3>dist.
      <3>A. CASE Mid >= Threshold
        <4>1. ENABLED <<ProbeLeft>>_vars
          BY <3>A, <3>nat, ExpandENABLED, SMT DEF ProbeLeft, Mid, vars
        <4> QED  BY <4>1, <3>dist
      <3>B. CASE Mid < Threshold
        <4>1. ENABLED <<ProbeRight>>_vars
          BY <3>B, <3>nat, ExpandENABLED, SMT DEF ProbeRight, Mid, vars
        <4> QED  BY <4>1, <3>dist
      <3>trich. Mid >= Threshold \/ Mid < Threshold
        BY <3>nat, ThresholdType
      <3> QED  BY <3>A, <3>B, <3>trich
    <2> QED  BY <2>i, <2>ii, <2>iii, Safety, PTL DEF Spec
  <1>dn. P(0)
    BY <1>base, <1>step, MaxProbesType, DownwardNatInduction
  <1>zero. Spec => [](MaxProbes - probes_taken = 0 => hi - lo < 2)
    <2>1. Inv => (MaxProbes - probes_taken = 0 => hi - lo < 2)
      <3>1. (MaxProbes - probes_taken = 0) => Pow2[MaxProbes - probes_taken] = Pow2[0]
        OBVIOUS
      <3> QED  BY <3>1, Pow2Zero, MaxProbesType DEF Inv, WidthExpBound, TypeInvariant
    <2> QED  BY <2>1, Safety, PTL DEF Spec
  <1> QED
    BY <1>dn, <1>zero, PTL DEF P, EventualConvergence
====
