---- MODULE SelectThenActuate_Proof ----
(* TLAPS proof of SelectThenActuate safety. The composition reuses the
   ActuationPass proof through an instance and proves the selection obligation
   around that owner. The argmax lemmas establish existence of the
   lowest-position maximizing candidate. *)
EXTENDS SelectThenActuate, FiniteSetTheorems, TLAPS

\* Candidates is finite (cfg sets Candidates = {c1, c2, c3}).
ASSUME CandidatesFinite == IsFiniteSet(Candidates)

\* Candidates is non-empty for the argmax to exist; the cfg always sets
\* Candidates to a non-empty set.
ASSUME CandidatesNonEmpty == Candidates # {}

\* MaxScore is a Nat; cfg sets MaxScore = 3.
ASSUME MaxScoreType == MaxScore \in Nat

\* NULL is not itself a candidate: needed so that Evaluate's CHOOSE result
\* (always \in Candidates) can be shown # NULL for ActuationScope', the same
\* sentinel-disjointness role QualityHierarchy_Proof.tla's NotANode plays
\* (STRUCTURE_ASSUMPTIONS.md). Neither CompetitiveSelectionHard nor ActuationPass
\* needs this ASSUME on its own: neither module has both concepts (a CHOOSE
\* result assigned into allocation, and a NULL sentinel gating actuation) in
\* play at once.
ASSUME NullNotCandidate == NULL \notin Candidates

\* ----------------------------------------------------------------------
\* Existence of an argmax over a finite non-empty candidate set.
\* ----------------------------------------------------------------------
LEMMA ArgmaxExists ==
    ASSUME NEW S, IsFiniteSet(S), S # {},
           NEW f, f \in [S -> Nat]
    PROVE  \E c \in S : \A other \in S : f[other] <= f[c]
  <1> DEFINE P(n) == \A T \in SUBSET S :
                       (Cardinality(T) = n /\ T # {})
                         => \E c \in T : \A other \in T : f[other] <= f[c]
  <1>1. P(0)
    <2> SUFFICES ASSUME NEW T \in SUBSET S, Cardinality(T) = 0, T # {}
                 PROVE  FALSE
      OBVIOUS
    <2>1. IsFiniteSet(T)  BY FS_Subset
    <2>2. T = {}          BY <2>1, FS_EmptySet
    <2> QED  BY <2>2
  <1>2. \A n \in Nat : P(n) => P(n+1)
    <2> SUFFICES ASSUME NEW n \in Nat, P(n),
                        NEW T \in SUBSET S, Cardinality(T) = n + 1, T # {}
                 PROVE  \E c \in T : \A other \in T : f[other] <= f[c]
      OBVIOUS
    <2>fin. IsFiniteSet(T)         BY FS_Subset
    <2>x.   PICK x \in T : TRUE    OBVIOUS
    <2> DEFINE Tp == T \ {x}
    <2>sub. Tp \in SUBSET S        OBVIOUS
    <2>card. Cardinality(Tp) = n
      BY <2>fin, <2>x, FS_RemoveElement
    <2>union. T = Tp \cup {x}      BY <2>x
    <2>fxNat. f[x] \in Nat         BY <2>x
    <2>A. CASE Tp = {}
      <3>1. T = {x}                          BY <2>union, <2>A
      <3>2. \A other \in {x} : f[other] <= f[x]  BY <2>fxNat
      <3> QED  BY <3>1, <3>2
    <2>B. CASE Tp # {}
      <3>1. \E c \in Tp : \A other \in Tp : f[other] <= f[c]
        BY <2>sub, <2>card, <2>B, P(n)
      <3>2. PICK cT \in Tp : \A other \in Tp : f[other] <= f[cT]  BY <3>1
      <3>3. cT \in T        BY <3>2, <2>union
      <3>4. f[cT] \in Nat   BY <3>2, <2>sub
      <3>cmp. f[x] <= f[cT] \/ f[cT] <= f[x]  BY <2>fxNat, <3>4
      <3>A. CASE f[x] <= f[cT]
        <4>1. \A other \in T : f[other] <= f[cT]
          <5> SUFFICES ASSUME NEW other \in T PROVE f[other] <= f[cT]  OBVIOUS
          <5>1. other \in Tp \/ other = x  BY <2>union
          <5>A. CASE other \in Tp  BY <5>A, <3>2
          <5>B. CASE other = x     BY <5>B, <3>A
          <5> QED  BY <5>1, <5>A, <5>B
        <4> QED  BY <3>3, <4>1
      <3>B. CASE f[cT] <= f[x]
        <4>1. \A other \in T : f[other] <= f[x]
          <5> SUFFICES ASSUME NEW other \in T PROVE f[other] <= f[x]  OBVIOUS
          <5>1. other \in Tp \/ other = x  BY <2>union
          <5>A. CASE other \in Tp
            <6>1. f[other] <= f[cT]  BY <5>A, <3>2
            <6>2. f[other] \in Nat   BY <5>A, <2>sub
            <6> QED  BY <6>1, <3>B, <6>2, <3>4, <2>fxNat
          <5>B. CASE other = x     BY <5>B, <2>fxNat
          <5> QED  BY <5>1, <5>A, <5>B
        <4>2. x \in T  BY <2>x
        <4> QED  BY <4>2, <4>1
      <3> QED  BY <3>cmp, <3>A, <3>B
    <2> QED  BY <2>A, <2>B
  <1>3. \A n \in Nat : P(n)  BY <1>1, <1>2, NatInduction
  <1>card. Cardinality(S) \in Nat  BY FS_CardinalityType
  <1>4. P(Cardinality(S))  BY <1>3, <1>card
  <1> QED  BY <1>4

LEMMA EvalArgmaxExists ==
    ASSUME NEW score_fn, score_fn \in [Candidates -> 0..MaxScore]
    PROVE  \E c \in Candidates : \A other \in Candidates : score_fn[other] <= score_fn[c]
  <1>1. score_fn \in [Candidates -> Nat]
    <2>1. 0..MaxScore \subseteq Nat  BY MaxScoreType
    <2>2. \A c \in Candidates : score_fn[c] \in Nat
      BY <2>1
    <2> QED  BY <2>2
  <1> QED  BY <1>1, CandidatesFinite, CandidatesNonEmpty, ArgmaxExists

\* ----------------------------------------------------------------------
\* Existence of the lowest-position member of the argmax set.
\* ----------------------------------------------------------------------
LEMMA WNType == WN \in Nat
  BY CandidatesFinite, FS_CardinalityType DEF WN

LEMMA WNPos == WN \in Nat /\ WN > 0
  <1>1. WN \in Nat  BY WNType
  <1>2. WN = 0 => Candidates = {}
    <2> SUFFICES ASSUME WN = 0 PROVE Candidates = {}  OBVIOUS
    <2>1. Cardinality(Candidates) = 0  BY DEF WN
    <2> QED  BY <2>1, CandidatesFinite, FS_EmptySet
  <1> QED  BY <1>1, <1>2, CandidatesNonEmpty

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
    BY <1>ex DEF WEnum
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
  <1> QED  BY <1>1, <1>2

LEMMA PosProp ==
  ASSUME NEW c \in Candidates
  PROVE  /\ Pos(c) \in 1..WN
         /\ WEnum[Pos(c)] = c
  <1>1. \E i \in 1..WN : WEnum[i] = c  BY WEnumBij
  <1> QED  BY <1>1 DEF Pos

LEMMA PosNat ==
  ASSUME NEW c \in Candidates
  PROVE  Pos(c) \in Nat
  <1>1. Pos(c) \in 1..WN  BY PosProp
  <1> QED  BY <1>1, WNType, FS_Interval

LEMMA MinExists ==
    ASSUME NEW S, IsFiniteSet(S), S # {},
           NEW f, f \in [S -> Nat]
    PROVE  \E c \in S : \A other \in S : f[c] <= f[other]
  <1> DEFINE P(n) == \A T \in SUBSET S :
                       (Cardinality(T) = n /\ T # {})
                         => \E c \in T : \A other \in T : f[c] <= f[other]
  <1>1. P(0)
    <2> SUFFICES ASSUME NEW T \in SUBSET S, Cardinality(T) = 0, T # {}
                 PROVE  FALSE
      OBVIOUS
    <2>1. IsFiniteSet(T)  BY FS_Subset
    <2>2. T = {}          BY <2>1, FS_EmptySet
    <2> QED  BY <2>2
  <1>2. \A n \in Nat : P(n) => P(n+1)
    <2> SUFFICES ASSUME NEW n \in Nat, P(n),
                        NEW T \in SUBSET S, Cardinality(T) = n + 1, T # {}
                 PROVE  \E c \in T : \A other \in T : f[c] <= f[other]
      OBVIOUS
    <2>fin. IsFiniteSet(T)         BY FS_Subset
    <2>x.   PICK x \in T : TRUE    OBVIOUS
    <2> DEFINE Tp == T \ {x}
    <2>sub. Tp \in SUBSET S        OBVIOUS
    <2>card. Cardinality(Tp) = n
      BY <2>fin, <2>x, FS_RemoveElement
    <2>union. T = Tp \cup {x}      BY <2>x
    <2>fxNat. f[x] \in Nat         BY <2>x
    <2>A. CASE Tp = {}
      <3>1. T = {x}                          BY <2>union, <2>A
      <3>2. \A other \in {x} : f[x] <= f[other]  BY <2>fxNat
      <3> QED  BY <3>1, <3>2
    <2>B. CASE Tp # {}
      <3>1. \E c \in Tp : \A other \in Tp : f[c] <= f[other]
        BY <2>sub, <2>card, <2>B, P(n)
      <3>2. PICK cT \in Tp : \A other \in Tp : f[cT] <= f[other]  BY <3>1
      <3>3. cT \in T        BY <3>2, <2>union
      <3>4. f[cT] \in Nat   BY <3>2, <2>sub
      <3>cmp. f[x] <= f[cT] \/ f[cT] <= f[x]  BY <2>fxNat, <3>4
      <3>A. CASE f[cT] <= f[x]
        <4>1. \A other \in T : f[cT] <= f[other]
          <5> SUFFICES ASSUME NEW other \in T PROVE f[cT] <= f[other]  OBVIOUS
          <5>1. other \in Tp \/ other = x  BY <2>union
          <5>A. CASE other \in Tp  BY <5>A, <3>2
          <5>B. CASE other = x     BY <5>B, <3>A
          <5> QED  BY <5>1, <5>A, <5>B
        <4> QED  BY <3>3, <4>1
      <3>B. CASE f[x] <= f[cT]
        <4>1. \A other \in T : f[x] <= f[other]
          <5> SUFFICES ASSUME NEW other \in T PROVE f[x] <= f[other]  OBVIOUS
          <5>1. other \in Tp \/ other = x  BY <2>union
          <5>A. CASE other \in Tp
            <6>1. f[cT] <= f[other]  BY <5>A, <3>2
            <6>2. f[other] \in Nat   BY <5>A, <2>sub
            <6> QED  BY <6>1, <3>B, <6>2, <3>4, <2>fxNat
          <5>B. CASE other = x     BY <5>B, <2>fxNat
          <5> QED  BY <5>1, <5>A, <5>B
        <4>2. x \in T  BY <2>x
        <4> QED  BY <4>2, <4>1
      <3> QED  BY <3>cmp, <3>A, <3>B
    <2> QED  BY <2>A, <2>B
  <1>3. \A n \in Nat : P(n)  BY <1>1, <1>2, NatInduction
  <1>card. Cardinality(S) \in Nat  BY FS_CardinalityType
  <1>4. P(Cardinality(S))  BY <1>3, <1>card
  <1> QED  BY <1>4

LEMMA WinnerOfExists ==
    ASSUME NEW score_fn, score_fn \in [Candidates -> 0..MaxScore]
    PROVE  \E c \in Candidates :
             /\ \A other \in Candidates : score_fn[other] <= score_fn[c]
             /\ \A other \in Candidates : score_fn[other] = score_fn[c] => Pos(c) <= Pos(other)
  <1> DEFINE Argmaxes == {c \in Candidates :
                            \A other \in Candidates : score_fn[other] <= score_fn[c]}
  <1>ne. Argmaxes # {}
    <2>1. \E c \in Candidates : \A other \in Candidates : score_fn[other] <= score_fn[c]
      BY EvalArgmaxExists
    <2> QED  BY <2>1
  <1>sub. Argmaxes \subseteq Candidates  OBVIOUS
  <1>fin. IsFiniteSet(Argmaxes)  BY <1>sub, CandidatesFinite, FS_Subset
  <1> DEFINE posFn == [c \in Argmaxes |-> Pos(c)]
  <1>posFn. posFn \in [Argmaxes -> Nat]
    <2>1. \A c \in Argmaxes : Pos(c) \in Nat  BY <1>sub, PosNat
    <2> QED  BY <2>1
  <1>min. \E w \in Argmaxes : \A other \in Argmaxes : posFn[w] <= posFn[other]
    BY <1>fin, <1>ne, <1>posFn, MinExists
  <1>2. PICK w \in Argmaxes : \A other \in Argmaxes : posFn[w] <= posFn[other]  BY <1>min
  <1>w1. w \in Candidates  BY <1>2, <1>sub
  <1>w2. \A other \in Candidates : score_fn[other] <= score_fn[w]  BY <1>2
  <1>3. \A other \in Candidates : score_fn[other] = score_fn[w] => Pos(w) <= Pos(other)
    <2> SUFFICES ASSUME NEW other \in Candidates, score_fn[other] = score_fn[w]
                 PROVE Pos(w) <= Pos(other)
      OBVIOUS
    <2>1. other \in Argmaxes
      <3>1. \A o2 \in Candidates : score_fn[o2] <= score_fn[w]  BY <1>2
      <3>2. \A o2 \in Candidates : score_fn[o2] <= score_fn[other]  BY <3>1
      <3> QED  BY <3>2
    <2>2. posFn[w] <= posFn[other]  BY <1>2, <2>1
    <2>3. posFn[w] = Pos(w)         BY <1>2
    <2>4. posFn[other] = Pos(other) BY <2>1
    <2> QED  BY <2>2, <2>3, <2>4
  <1> QED  BY <1>w1, <1>w2, <1>3

\* ----------------------------------------------------------------------
\* TypeInvariant and both component obligations form the inductive invariant.
\* ----------------------------------------------------------------------

APP == INSTANCE ActuationPass_Proof WITH
           Seats      <- Seats,
           Resources  <- Candidates,
           NULL       <- NULL,
           allocation <- allocation,
           effects    <- effects,
           complete   <- complete

ScoreType == scores \in [Seats -> [Candidates -> 0..MaxScore]]

\* APP!Inv is the canonical ActuationPass inductive invariant. This
\* composition adds score typing and winner optimality around that owner.
Inv == APP!Inv /\ ScoreType /\ WinnerOptimality

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. APP!Init  BY DEF Init, APP!Init
  <1>2. APP!Inv  BY <1>1, APP!InitInv
  <1>3. ScoreType
    BY MaxScoreType DEF Init, ScoreType
  <1>4. WinnerOptimality
    BY DEF Init, WinnerOptimality
  <1> QED  BY <1>2, <1>3, <1>4 DEF Inv

\* Every composition step is an ActuationPass step or stutter at the
\* ActuationPass projection.
LEMMA CompositeStepRefinesActuation ==
    Inv /\ [Next]_vars => [APP!Next]_APP!vars
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [APP!Next]_APP!vars  OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars, APP!vars
  <1>X. CASE Next
    <2>next. Next  BY <1>X
    <2>A. CASE \E s \in Seats : Evaluate(s)
      <3> SUFFICES ASSUME NEW s \in Seats, Evaluate(s)
                   PROVE [APP!Next]_APP!vars
        BY <2>A
      <3>scoresType. scores[s] \in [Candidates -> 0..MaxScore]
        BY DEF Inv, ScoreType
      <3>wexists. \E c \in Candidates :
                    /\ \A other \in Candidates : scores[s][other] <= scores[s][c]
                    /\ \A other \in Candidates :
                          scores[s][other] = scores[s][c] => Pos(c) <= Pos(other)
        BY <3>scoresType, WinnerOfExists
      <3> DEFINE best == CHOOSE c \in Candidates :
                    /\ \A other \in Candidates : scores[s][other] <= scores[s][c]
                    /\ \A other \in Candidates :
                          scores[s][other] = scores[s][c] => Pos(c) <= Pos(other)
      <3>best. best \in Candidates  BY <3>wexists
      <3>1. AP!Allocate(s, best)  BY DEF Evaluate
      <3>2. APP!Allocate(s, best)
        BY <3>1 DEF AP!Allocate, APP!Allocate
      <3>3. APP!Next  BY <3>best, <3>2 DEF APP!Next
      <3> QED  BY <3>3
    <2>B. CASE \E s \in Seats, c \in Candidates, v \in 0..MaxScore :
                  UpdateScore(s, c, v)
      <3> SUFFICES ASSUME NEW s \in Seats, NEW c \in Candidates,
                          NEW v \in 0..MaxScore, UpdateScore(s, c, v)
                   PROVE [APP!Next]_APP!vars
        BY <2>B
      <3>A. CASE allocation[s] /= NULL
        BY <3>A DEF UpdateScore, AP!Deallocate, APP!Deallocate, APP!Next
      <3>B. CASE allocation[s] = NULL
        BY <3>B DEF UpdateScore, actuationVars, APP!vars
      <3> QED  BY <3>A, <3>B
    <2>C. CASE \E s \in Seats : Actuate(s)
      BY <2>C DEF Actuate, AP!Actuate, APP!Actuate, APP!Next
    <2>D. CASE Finish
      BY <2>D DEF Finish, AP!Finish, APP!Finish, APP!Next
    <2>cases. \/ (\E s \in Seats : Evaluate(s))
               \/ ((\E s \in Seats, c \in Candidates, v \in 0..MaxScore :
                         UpdateScore(s, c, v))
                   \/ ((\E s \in Seats : Actuate(s)) \/ Finish))
      BY <2>next DEF Next
    <2> QED  BY <2>cases, <2>A, <2>B, <2>C, <2>D
  <1> QED  BY <1>0, <1>X

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1>appStep. [APP!Next]_APP!vars  BY CompositeStepRefinesActuation
  <1>apInv. APP!Inv'  BY <1>appStep, APP!NextInv DEF Inv
  <1>0. CASE UNCHANGED vars
    BY <1>0, <1>apInv DEF Inv, ScoreType, WinnerOptimality, vars
  <1>X. CASE Next
    <2>next. Next  BY <1>X
    <2>A. CASE \E s \in Seats : Evaluate(s)
      <3> SUFFICES ASSUME NEW s \in Seats, Evaluate(s) PROVE Inv'
        BY <2>A
      <3> USE DEF Evaluate
      <3>scoresType. scores[s] \in [Candidates -> 0..MaxScore]
        BY DEF Inv, ScoreType
      <3>allocationType. allocation \in [Seats -> Candidates \cup {NULL}]
        BY DEF Inv, APP!Inv, APP!TypeInvariant
      <3>wexists. \E c \in Candidates :
                    /\ \A other \in Candidates : scores[s][other] <= scores[s][c]
                    /\ \A other \in Candidates :
                          scores[s][other] = scores[s][c] => Pos(c) <= Pos(other)
        BY <3>scoresType, WinnerOfExists
      <3> DEFINE best == CHOOSE c \in Candidates :
                    /\ \A other \in Candidates : scores[s][other] <= scores[s][c]
                    /\ \A other \in Candidates :
                          scores[s][other] = scores[s][c] => Pos(c) <= Pos(other)
      <3>best. /\ best \in Candidates
                /\ \A other \in Candidates : scores[s][other] <= scores[s][best]
        BY <3>wexists
      <3>allocPrime. allocation' = [allocation EXCEPT ![s] = best]
        BY DEF Evaluate, AP!Allocate
      <3>allocAt. allocation'[s] = best
        BY <3>allocPrime, <3>allocationType
      <3>scoresPrime. scores' = scores  BY DEF Evaluate
      <3>oldScoreType. ScoreType  BY DEF Inv
      <3>1. ScoreType'  BY <3>scoresPrime, <3>oldScoreType DEF ScoreType
      <3>2. WinnerOptimality'
        <4> SUFFICES ASSUME NEW t \in Seats, allocation'[t] /= NULL,
                            NEW c \in Candidates
                     PROVE scores'[t][c] <= scores'[t][allocation'[t]]
          BY DEF WinnerOptimality
        <4>A. CASE t = s
          <5>eq. t = s  BY <4>A
          <5>1. allocation'[t] = best  BY <5>eq, <3>allocAt
          <5>2. scores'[t] = scores[s]  BY <4>A, <3>scoresPrime
          <5> QED  BY <5>1, <5>2, <3>best
        <4>B. CASE t # s
          <5>1. allocation'[t] = allocation[t]  BY <4>B, <3>allocPrime
          <5>2. scores'[t] = scores[t]  BY <3>scoresPrime
          <5> QED  BY <5>1, <5>2 DEF Inv, WinnerOptimality
        <4> QED  BY <4>A, <4>B
      <3> QED  BY <1>apInv, <3>1, <3>2 DEF Inv
    <2>B. CASE \E s \in Seats, c \in Candidates, v \in 0..MaxScore :
                  UpdateScore(s, c, v)
      <3> SUFFICES ASSUME NEW s \in Seats, NEW c \in Candidates,
                          NEW v \in 0..MaxScore, UpdateScore(s, c, v)
                   PROVE Inv'
        BY <2>B
      <3> USE DEF UpdateScore
      <3>scoreMapType. ScoreType  BY DEF Inv
      <3>allocationType. allocation \in [Seats -> Candidates \cup {NULL}]
        BY DEF Inv, APP!Inv, APP!TypeInvariant
      <3>scoresPrime. scores' = [scores EXCEPT ![s][c] = v]
        BY DEF UpdateScore
      <3>allocPrime. allocation'[s] = NULL
        <4>A. CASE allocation[s] /= NULL
          BY <4>A, <3>allocationType
             DEF UpdateScore, AP!Deallocate, AP!vars, actuationVars
        <4>B. CASE allocation[s] = NULL
          BY <4>B DEF UpdateScore, actuationVars
        <4> QED  BY <4>A, <4>B
      <3>allocFrame. \A t \in Seats \ {s} : allocation'[t] = allocation[t]
        <4> SUFFICES ASSUME NEW t \in Seats \ {s}
                     PROVE allocation'[t] = allocation[t]
          OBVIOUS
        <4>A. CASE allocation[s] /= NULL
          BY <4>A, <3>allocationType
             DEF UpdateScore, AP!Deallocate, AP!vars, actuationVars
        <4>B. CASE allocation[s] = NULL
          BY <4>B DEF UpdateScore, actuationVars
        <4> QED  BY <4>A, <4>B
      <3>1. ScoreType'
        BY <3>scoresPrime, <3>scoreMapType DEF ScoreType
      <3>2. WinnerOptimality'
        <4> SUFFICES ASSUME NEW t \in Seats, allocation'[t] /= NULL,
                            NEW d \in Candidates
                     PROVE scores'[t][d] <= scores'[t][allocation'[t]]
          BY DEF WinnerOptimality
        <4>1. t # s  BY <3>allocPrime
        <4>2. allocation'[t] = allocation[t]  BY <4>1, <3>allocFrame
        <4>3. scores'[t] = scores[t]  BY <4>1, <3>scoresPrime
        <4> QED  BY <4>2, <4>3 DEF Inv, WinnerOptimality
      <3> QED  BY <1>apInv, <3>1, <3>2 DEF Inv
    <2>C. CASE \E s \in Seats : Actuate(s)
      <3> SUFFICES ASSUME NEW s \in Seats, Actuate(s) PROVE Inv'
        BY <2>C
      <3>1. allocation' = allocation  BY DEF Actuate, AP!Actuate
      <3>2. scores' = scores           BY DEF Actuate
      <3> QED  BY <1>apInv, <3>1, <3>2 DEF Inv, ScoreType, WinnerOptimality
    <2>D. CASE Finish
      <3>1. allocation' = allocation  BY <2>D DEF Finish, AP!Finish
      <3>2. scores' = scores           BY <2>D DEF Finish
      <3> QED  BY <1>apInv, <3>1, <3>2 DEF Inv, ScoreType, WinnerOptimality
    <2>cases. \/ (\E s \in Seats : Evaluate(s))
               \/ ((\E s \in Seats, c \in Candidates, v \in 0..MaxScore :
                         UpdateScore(s, c, v))
                   \/ ((\E s \in Seats : Actuate(s)) \/ Finish))
      BY <2>next DEF Next
    <2> QED  BY <2>cases, <2>A, <2>B, <2>C, <2>D
  <1> QED  BY <1>0, <1>X

LEMMA PublishedInvariant ==
    Inv => TypeInvariant /\ CompositionInvariant
  <1> SUFFICES ASSUME Inv PROVE TypeInvariant /\ CompositionInvariant  OBVIOUS
  <1>1. APP!TypeInvariant /\ APP!EffectFidelity /\ APP!PassCompleteness
    BY DEF Inv, APP!Inv
  <1>2. APP!ActuationScope
    BY <1>1, APP!ScopeFromFidelity
  <1>3. /\ AP!TypeInvariant
          /\ AP!EffectFidelity
          /\ AP!PassCompleteness
          /\ AP!ActuationScope
    BY <1>1, <1>2
       DEF AP!TypeInvariant, AP!EffectFidelity, AP!PassCompleteness,
           AP!ActuationScope, APP!TypeInvariant, APP!EffectFidelity,
           APP!PassCompleteness, APP!ActuationScope, AP!Actuated, APP!Actuated
  <1> QED
    BY <1>3 DEF Inv, ScoreType, TypeInvariant, CompositionInvariant,
                         EffectFidelity, ActuationScope, PassCompleteness

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                  BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant
  BY Safety, PublishedInvariant, PTL

THEOREM CompositionSafety == Spec => []CompositionInvariant
  BY Safety, PublishedInvariant, PTL

THEOREM ActuationScopeSafety == Spec => []ActuationScope
  BY Safety, PublishedInvariant, PTL DEF CompositionInvariant

THEOREM EffectFidelitySafety == Spec => []EffectFidelity
  BY Safety, PublishedInvariant, PTL DEF CompositionInvariant

THEOREM PassCompletenessSafety == Spec => []PassCompleteness
  BY Safety, PublishedInvariant, PTL DEF CompositionInvariant

THEOREM WinnerOptimalitySafety == Spec => []WinnerOptimality
  BY Safety, PublishedInvariant, PTL DEF CompositionInvariant
====
