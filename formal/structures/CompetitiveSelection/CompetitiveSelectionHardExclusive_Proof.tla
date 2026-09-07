---- MODULE CompetitiveSelectionHardExclusive_Proof ----
(* TLAPS proof of CompetitiveSelectionHardExclusive safety: TypeInvariant,
   MutualExclusion, WinnerOptimality, WinnerTieBreak.

   ArgmaxExists and MinExists are generic over a finite non-empty set with a
   natural-valued function, so they apply to each availability pool.
   PoolWinnerExists selects the lowest-position argmax from that pool.

   Evaluate's `best` is
   drawn from Available(s), which by definition excludes every other seat's
   holding; that single fact discharges MutualExclusion.  Availability is
   monotone under Evaluate: awarding a seat only removes a candidate from
   every other seat's pool, and the awarding seat's own pool is untouched by
   its own entry -- which is what preserves the two optimality invariants for
   the seats that are not moving.  UpdateScore clears the whole allocation, so
   all three obligations are vacuous in that case.

   `NULL \notin Candidates` is explicit because
   Available(s) is defined by comparing candidates against other seats'
   holdings, and a NULL that were itself a candidate would make an empty seat
   exclude the sentinel from every other pool.  It is the ordinary sentinel
   condition and the .cfg satisfies it.                                     *)
EXTENDS CompetitiveSelectionHardExclusive, FiniteSetTheorems, TLAPS

\* Finiteness and non-emptiness support argmax and enumeration witnesses.
ASSUME CandidatesFinite == IsFiniteSet(Candidates)
ASSUME CandidatesNonEmpty == Candidates # {}

\* Scores range over naturals.
ASSUME MaxScoreType == MaxScore \in Nat

\* The sentinel condition (see the header).
ASSUME NullNotCandidate == NULL \notin Candidates

\* ----------------------------------------------------------------------
\* Generic extrema over finite non-empty sets.
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
      <3>1. T = {x}                              BY <2>union, <2>A
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
      <3>1. T = {x}                              BY <2>union, <2>A
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

\* ----------------------------------------------------------------------
\* Candidate-position enumeration and inverse.
\* ----------------------------------------------------------------------
LEMMA WNType == WN \in Nat
  BY CandidatesFinite, FS_CardinalityType DEF WN

LEMMA WEnumBij ==
  /\ WEnum \in [1..WN -> Candidates]
  /\ \A c \in Candidates : \E i \in 1..WN : WEnum[i] = c
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
  <1> QED  BY CandidateOrderType DEF WEnum

LEMMA PosNat ==
  ASSUME NEW c \in Candidates
  PROVE  Pos(c) \in Nat
  <1>1. \E i \in 1..WN : WEnum[i] = c  BY WEnumBij
  <1>2. Pos(c) \in 1..WN               BY <1>1 DEF Pos
  <1> QED  BY <1>2, WNType, FS_Interval

\* ----------------------------------------------------------------------
\* The lowest-position argmax exists over every non-empty candidate subset.
\* ----------------------------------------------------------------------
LEMMA PoolWinnerExists ==
    ASSUME NEW P, P \subseteq Candidates, P # {},
           NEW score_fn, score_fn \in [Candidates -> 0..MaxScore]
    PROVE  \E c \in P :
             /\ \A other \in P : score_fn[other] <= score_fn[c]
             /\ \A other \in P : score_fn[other] = score_fn[c] => Pos(c) <= Pos(other)
  <1>fin. IsFiniteSet(P)  BY CandidatesFinite, FS_Subset
  <1> DEFINE g == [c \in P |-> score_fn[c]]
  <1>g. g \in [P -> Nat]
    <2>1. 0..MaxScore \subseteq Nat  BY MaxScoreType
    <2>2. \A c \in P : score_fn[c] \in Nat  BY <2>1
    <2> QED  BY <2>2
  <1> DEFINE Argmaxes == {c \in P : \A other \in P : score_fn[other] <= score_fn[c]}
  <1>ne. Argmaxes # {}
    <2>1. \E c \in P : \A other \in P : g[other] <= g[c]
      BY <1>fin, <1>g, ArgmaxExists
    <2>2. \A c \in P : g[c] = score_fn[c]  OBVIOUS
    <2> QED  BY <2>1, <2>2
  <1>sub. Argmaxes \subseteq P  OBVIOUS
  <1>afin. IsFiniteSet(Argmaxes)  BY <1>fin, <1>sub, FS_Subset
  <1> DEFINE posFn == [c \in Argmaxes |-> Pos(c)]
  <1>posFn. posFn \in [Argmaxes -> Nat]
    <2>1. \A c \in Argmaxes : Pos(c) \in Nat  BY <1>sub, PosNat
    <2> QED  BY <2>1
  <1>min. \E w \in Argmaxes : \A other \in Argmaxes : posFn[w] <= posFn[other]
    BY <1>afin, <1>ne, <1>posFn, MinExists
  <1>2. PICK w \in Argmaxes : \A other \in Argmaxes : posFn[w] <= posFn[other]  BY <1>min
  <1>w1. w \in P  BY <1>2, <1>sub
  <1>w2. \A other \in P : score_fn[other] <= score_fn[w]  BY <1>2
  <1>3. \A other \in P : score_fn[other] = score_fn[w] => Pos(w) <= Pos(other)
    <2> SUFFICES ASSUME NEW other \in P, score_fn[other] = score_fn[w]
                 PROVE Pos(w) <= Pos(other)
      OBVIOUS
    <2>1. other \in Argmaxes
      <3>1. \A o2 \in P : score_fn[o2] <= score_fn[w]  BY <1>2
      <3>2. \A o2 \in P : score_fn[o2] <= score_fn[other]  BY <3>1
      <3> QED  BY <3>2
    <2>2. posFn[w] <= posFn[other]  BY <1>2, <2>1
    <2>3. posFn[w] = Pos(w)         BY <1>2
    <2>4. posFn[other] = Pos(other) BY <2>1
    <2> QED  BY <2>2, <2>3, <2>4
  <1> QED  BY <1>w1, <1>w2, <1>3

\* ----------------------------------------------------------------------
\* The combined inductive invariant.
\* ----------------------------------------------------------------------
Inv == TypeInvariant /\ MutualExclusion /\ WinnerOptimality /\ WinnerTieBreak

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1> USE DEF Init
  <1>1. TypeInvariant
    BY MaxScoreType DEF TypeInvariant
  <1>2. MutualExclusion
    \* every seat holds NULL, so the antecedent is false.
    BY DEF MutualExclusion
  <1>3. WinnerOptimality
    BY DEF WinnerOptimality
  <1>4. WinnerTieBreak
    BY DEF WinnerTieBreak
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, MutualExclusion, WinnerOptimality, WinnerTieBreak
  <1>0. CASE UNCHANGED vars
    \* Available is a state function of `allocation`, so the stutter case has to
    \* unfold it to see that the pool is unchanged too.
    BY <1>0 DEF vars, Available
  \* ---- Evaluate(s) ------------------------------------------------------
  <1>A. CASE \E s \in Seats : Evaluate(s)
    <2> SUFFICES ASSUME NEW s \in Seats, Evaluate(s) PROVE Inv'  BY <1>A
    <2> USE DEF Evaluate
    <2>free. allocation[s] = NULL                        BY DEF Evaluate
    <2>pne.  Available(s) # {}                           BY DEF Evaluate
    <2>psub. Available(s) \subseteq Candidates           BY DEF Available
    <2>sc.   scores[s] \in [Candidates -> 0..MaxScore]   BY DEF TypeInvariant
    <2>wex. \E c \in Available(s) :
              /\ \A other \in Available(s) : scores[s][other] <= scores[s][c]
              /\ \A other \in Available(s) :
                    scores[s][other] = scores[s][c] => Pos(c) <= Pos(other)
      BY <2>psub, <2>pne, <2>sc, PoolWinnerExists
    <2> DEFINE best == CHOOSE c \in Available(s) :
                  /\ \A other \in Available(s) : scores[s][other] <= scores[s][c]
                  /\ \A other \in Available(s) :
                        scores[s][other] = scores[s][c] => Pos(c) <= Pos(other)
    <2>best. /\ best \in Available(s)
             /\ \A other \in Available(s) : scores[s][other] <= scores[s][best]
             /\ \A other \in Available(s) :
                   scores[s][other] = scores[s][best] => Pos(best) <= Pos(other)
      BY <2>wex
    <2>bc.  best \in Candidates                          BY <2>best, <2>psub
    <2>bex. \A t \in Seats \ {s} : allocation[t] /= best  BY <2>best DEF Available
    <2>ap.  allocation' = [allocation EXCEPT ![s] = best]  BY DEF Evaluate
    <2>sp.  scores' = scores                              BY DEF Evaluate
    <2>at.  allocation \in [Seats -> Candidates \cup {NULL}]  BY DEF TypeInvariant
    <2>pt.  \A t \in Seats : allocation'[t] = IF t = s THEN best ELSE allocation[t]
      BY <2>ap, <2>at
    \* Awarding s only removes `best` from the other
    \* seats' pools; s's own pool does not mention its own entry at all.
    <2>mono. \A t \in Seats : Available(t)' \subseteq Available(t)
      <3> SUFFICES ASSUME NEW t \in Seats, NEW c \in Available(t)'
                   PROVE  c \in Available(t)
        OBVIOUS
      <3>1. c \in Candidates                              BY DEF Available
      <3>2. \A u \in Seats \ {t} : allocation'[u] /= c     BY DEF Available
      <3>3. \A u \in Seats \ {t} : allocation[u] /= c
        <4> SUFFICES ASSUME NEW u \in Seats \ {t} PROVE allocation[u] /= c  OBVIOUS
        <4>A. CASE u = s
          <5>1. allocation[u] = NULL   BY <4>A, <2>free
          <5> QED  BY <5>1, <3>1, NullNotCandidate
        <4>B. CASE u /= s
          <5>1. allocation'[u] = allocation[u]  BY <4>B, <2>pt
          <5> QED  BY <5>1, <3>2
        <4> QED  BY <4>A, <4>B
      <3> QED  BY <3>1, <3>3 DEF Available
    <2>selfsame. Available(s)' = Available(s)
      <3>1. \A u \in Seats \ {s} : allocation'[u] = allocation[u]  BY <2>pt
      <3> QED  BY <3>1 DEF Available
    <2>1. TypeInvariant'
      <3>1. allocation' \in [Seats -> Candidates \cup {NULL}]
        <4> SUFFICES ASSUME NEW t \in Seats
                     PROVE allocation'[t] \in Candidates \cup {NULL}
          OBVIOUS
        <4>1. allocation'[t] = IF t = s THEN best ELSE allocation[t]  BY <2>pt
        <4> QED  BY <4>1, <2>bc, <2>at
      <3> QED  BY <3>1, <2>sp DEF TypeInvariant
    <2>2. MutualExclusion'
      <3> SUFFICES ASSUME NEW t1 \in Seats, NEW t2 \in Seats,
                          t1 /= t2, allocation'[t1] /= NULL
                   PROVE allocation'[t1] /= allocation'[t2]
        BY DEF MutualExclusion
      <3>A. CASE t1 = s
        <4>0. t2 /= s                                BY <3>A
        <4>1. allocation'[t1] = best                 BY <3>A, <2>pt
        <4>2. allocation'[t2] = allocation[t2]       BY <4>0, <2>pt
        <4> QED  BY <4>1, <4>2, <2>bex, <4>0
      <3>B. CASE t2 = s
        <4>0. t1 /= s                                BY <3>B
        <4>1. allocation'[t2] = best                 BY <3>B, <2>pt
        <4>2. allocation'[t1] = allocation[t1]       BY <4>0, <2>pt
        <4> QED  BY <4>1, <4>2, <2>bex, <4>0
      <3>C. CASE t1 /= s /\ t2 /= s
        <4>1. allocation'[t1] = allocation[t1]       BY <3>C, <2>pt
        <4>2. allocation'[t2] = allocation[t2]       BY <3>C, <2>pt
        <4> QED  BY <4>1, <4>2 DEF MutualExclusion
      <3> QED  BY <3>A, <3>B, <3>C
    <2>3. WinnerOptimality'
      <3> SUFFICES ASSUME NEW t \in Seats, allocation'[t] /= NULL,
                          NEW c \in Available(t)'
                   PROVE scores'[t][c] <= scores'[t][allocation'[t]]
        BY DEF WinnerOptimality
      <3>A. CASE t = s
        <4>1. allocation'[t] = best        BY <3>A, <2>pt
        <4>2. c \in Available(s)           BY <3>A, <2>selfsame
        <4>3. scores[s][c] <= scores[s][best]  BY <4>2, <2>best
        <4> QED  BY <4>1, <4>3, <3>A, <2>sp
      <3>B. CASE t /= s
        <4>1. allocation'[t] = allocation[t]   BY <3>B, <2>pt
        <4>2. c \in Available(t)               BY <2>mono
        <4>3. scores[t][c] <= scores[t][allocation[t]]
          BY <4>1, <4>2 DEF WinnerOptimality
        <4> QED  BY <4>1, <4>3, <2>sp
      <3> QED  BY <3>A, <3>B
    <2>4. WinnerTieBreak'
      <3> SUFFICES ASSUME NEW t \in Seats, allocation'[t] /= NULL,
                          NEW c \in Available(t)',
                          scores'[t][c] = scores'[t][allocation'[t]]
                   PROVE Pos(allocation'[t]) <= Pos(c)
        BY DEF WinnerTieBreak
      <3>A. CASE t = s
        <4>1. allocation'[t] = best        BY <3>A, <2>pt
        <4>2. c \in Available(s)           BY <3>A, <2>selfsame
        <4>3. scores[s][c] = scores[s][best]  BY <4>1, <3>A, <2>sp
        <4>4. Pos(best) <= Pos(c)          BY <4>2, <4>3, <2>best
        <4> QED  BY <4>1, <4>4
      <3>B. CASE t /= s
        <4>1. allocation'[t] = allocation[t]   BY <3>B, <2>pt
        <4>2. c \in Available(t)               BY <2>mono
        <4>3. scores[t][c] = scores[t][allocation[t]]  BY <4>1, <2>sp
        <4>4. Pos(allocation[t]) <= Pos(c)
          BY <4>1, <4>2, <4>3 DEF WinnerTieBreak
        <4> QED  BY <4>1, <4>4
      <3> QED  BY <3>A, <3>B
    <2> QED  BY <2>1, <2>2, <2>3, <2>4 DEF Inv
  \* ---- UpdateScore ------------------------------------------------------
  <1>B. CASE \E s \in Seats, c \in Candidates, v \in 0..MaxScore : UpdateScore(s, c, v)
    <2> SUFFICES ASSUME NEW s \in Seats, NEW c \in Candidates, NEW v \in 0..MaxScore,
                        UpdateScore(s, c, v)
                 PROVE Inv'
      BY <1>B
    <2> USE DEF UpdateScore
    <2>ap. allocation' = [t \in Seats |-> NULL]           BY DEF UpdateScore
    <2>sp. scores' = [scores EXCEPT ![s][c] = v]          BY DEF UpdateScore
    <2>null. \A t \in Seats : allocation'[t] = NULL       BY <2>ap
    <2>1. TypeInvariant'
      <3>1. allocation' \in [Seats -> Candidates \cup {NULL}]  BY <2>ap
      <3>2. scores' \in [Seats -> [Candidates -> 0..MaxScore]]
        <4> SUFFICES ASSUME NEW t \in Seats
                     PROVE scores'[t] \in [Candidates -> 0..MaxScore]
          OBVIOUS
        <4>st. scores \in [Seats -> [Candidates -> 0..MaxScore]]  BY DEF TypeInvariant
        <4>A. CASE t = s
          <5>1. scores'[s] = [scores[s] EXCEPT ![c] = v]  BY <2>sp, <4>st
          <5>2. scores[s] \in [Candidates -> 0..MaxScore] BY <4>st
          <5> QED  BY <4>A, <5>1, <5>2
        <4>B. CASE t /= s
          <5>1. scores'[t] = scores[t]  BY <4>B, <2>sp, <4>st
          <5> QED  BY <5>1, <4>st
        <4> QED  BY <4>A, <4>B
      <3> QED  BY <3>1, <3>2 DEF TypeInvariant
    <2>2. MutualExclusion'   BY <2>null DEF MutualExclusion
    <2>3. WinnerOptimality'  BY <2>null DEF WinnerOptimality
    <2>4. WinnerTieBreak'    BY <2>null DEF WinnerTieBreak
    <2> QED  BY <2>1, <2>2, <2>3, <2>4 DEF Inv
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                  BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'   BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

\* Per-invariant safety corollaries.
THEOREM TypeSafety == Spec => []TypeInvariant                  BY Safety, PTL DEF Inv
THEOREM MutualExclusionSafety == Spec => []MutualExclusion     BY Safety, PTL DEF Inv
THEOREM WinnerOptimalitySafety == Spec => []WinnerOptimality   BY Safety, PTL DEF Inv
THEOREM WinnerTieBreakSafety == Spec => []WinnerTieBreak       BY Safety, PTL DEF Inv
====
