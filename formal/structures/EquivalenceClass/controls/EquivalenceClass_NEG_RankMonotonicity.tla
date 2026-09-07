---- MODULE EquivalenceClass_NEG_RankMonotonicity ----
\* Negative control for RankMonotonicity. In the marked equal-rank branch, rb
\* becomes a child of ra but rb's rank is incremented. With only
\* RankMonotonicity declared, TLC must report that invariant violated.
\* Outside the marked replacement, executable formulas match the carrier.

EXTENDS Naturals, FiniteSets

CONSTANTS
    Elements,
    MaxOps

VARIABLES
    parent,
    rnk,
    ops_done

vars == <<parent, rnk, ops_done>>

RepFun[k \in 0..(MaxOps + 1)] ==
    IF k = 0 THEN [e \in Elements |-> e]
    ELSE [e \in Elements |-> IF parent[e] = e THEN e
                             ELSE RepFun[k - 1][parent[e]]]

Rep(e) == RepFun[MaxOps + 1][e]

TypeInvariant ==
    /\ parent \in [Elements -> Elements]
    /\ rnk    \in [Elements -> Nat]
    /\ ops_done \in Nat

RepresentativeIdempotence ==
    \A e \in Elements : Rep(e) = Rep(Rep(e))

Symmetry ==
    \A a \in Elements : \A b \in Elements :
        Rep(a) = Rep(b) => Rep(b) = Rep(a)

Transitivity ==
    \A a \in Elements : \A b \in Elements : \A c \in Elements :
        (Rep(a) = Rep(b) /\ Rep(b) = Rep(c)) => Rep(a) = Rep(c)

RankMonotonicity ==
    \A e \in Elements :
        parent[e] /= e => rnk[e] <= rnk[parent[e]]

RepresentativeRootedness ==
    \A e \in Elements : parent[Rep(e)] = Rep(e)

Init ==
    /\ parent = [e \in Elements |-> e]
    /\ rnk    = [e \in Elements |-> 0]
    /\ ops_done = 0

Union(a, b) ==
    /\ ops_done < MaxOps
    /\ LET ra == Rep(a)
           rb == Rep(b)
       IN  /\ ra /= rb
           /\ IF rnk[ra] < rnk[rb]
              THEN /\ parent' = [parent EXCEPT ![ra] = rb]
                   /\ rnk'   = rnk
              ELSE IF rnk[ra] > rnk[rb]
              THEN /\ parent' = [parent EXCEPT ![rb] = ra]
                   /\ rnk'   = rnk
\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
              ELSE \* MUTATED: at equal rank it is rb's rank that is incremented, not ra's
                   /\ parent' = [parent EXCEPT ![rb] = ra]
                   /\ rnk'   = [rnk EXCEPT ![rb] = rnk[rb] + 1]
\* ---- MUTATION ENDS.
    /\ ops_done' = ops_done + 1

Idle ==
    /\ ops_done >= MaxOps
    /\ UNCHANGED vars

Next ==
    \/ \E a \in Elements, b \in Elements : Union(a, b)
    \/ Idle

Spec == Init /\ [][Next]_vars

====
