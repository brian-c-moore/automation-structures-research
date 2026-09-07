---- MODULE EquivalenceClass ----
(* Union-find with union by rank and no path compression.

   parent and rnk encode the forest; ops_done counts successful Union steps.
   Rep is a bounded derived operator, not a state-changing Find action.

   The checked structural obligations are:
     RepresentativeIdempotence -- applying Rep to a representative is stable;
     RankMonotonicity           -- a non-root does not outrank its parent;
     RepresentativeRootedness  -- Rep returns a parent fixed point.

   Symmetry and Transitivity state properties of equality between Rep values;
   they are proved but are not independent controlled obligations. Runtime
   complexity and path compression are outside this model.
*)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Elements,   \* element set; the TLC configuration supplies a finite instance
    MaxOps      \* bound on number of union operations performed

VARIABLES
    parent,      \* parent[e] in Elements — parent pointer; root if parent[e]=e
    rnk,         \* rnk[e] in Nat — union-by-rank value
    ops_done     \* number of union operations performed so far

vars == <<parent, rnk, ops_done>>

\* Rep: root of element e under the parent array (path compression not modelled).
\* RepFun[k] gives the representative after at most k steps; MaxOps+1 steps
\* suffice because every reachable state is acyclic and rnk[e] <= ops_done <= MaxOps.
RepFun[k \in 0..(MaxOps + 1)] ==
    IF k = 0 THEN [e \in Elements |-> e]
    ELSE [e \in Elements |-> IF parent[e] = e THEN e
                             ELSE RepFun[k - 1][parent[e]]]

Rep(e) == RepFun[MaxOps + 1][e]

\* ---- Type invariant -------------------------------------------------------

TypeInvariant ==
    /\ parent \in [Elements -> Elements]
    /\ rnk    \in [Elements -> Nat]
    /\ ops_done \in Nat

\* ---- Safety invariants ----------------------------------------------------

\* Applying Rep to a derived representative leaves it unchanged.
RepresentativeIdempotence ==
    \A e \in Elements : Rep(e) = Rep(Rep(e))

\* This follows from symmetry of equality for any Rep. It is documentation of
\* the equivalence relation, not a checked invariant or controlled obligation.
\* Structural representative content is carried by RepresentativeIdempotence
\* and RepresentativeRootedness.
Symmetry ==
    \A a \in Elements : \A b \in Elements :
        Rep(a) = Rep(b) => Rep(b) = Rep(a)

\* This follows from transitivity of equality for any Rep. It is documentation
\* of the equivalence relation, not a checked invariant or controlled
\* obligation.
Transitivity ==
    \A a \in Elements : \A b \in Elements : \A c \in Elements :
        (Rep(a) = Rep(b) /\ Rep(b) = Rep(c)) => Rep(a) = Rep(c)

\* Rank is monotone up the parent pointers: an element that is not its own
\* parent is ranked no higher than its parent.
RankMonotonicity ==
    \A e \in Elements :
        parent[e] /= e => rnk[e] <= rnk[parent[e]]

\* Rep(e) is a root of the parent forest.
RepresentativeRootedness ==
    \A e \in Elements : parent[Rep(e)] = Rep(e)

\* ---- Init -----------------------------------------------------------------

Init ==
    /\ parent = [e \in Elements |-> e]   \* each element is its own root
    /\ rnk    = [e \in Elements |-> 0]   \* all ranks start at 0
    /\ ops_done = 0

\* ---- Actions --------------------------------------------------------------

\* Union(a,b): merge the classes of a and b using union-by-rank.
Union(a, b) ==
    /\ ops_done < MaxOps
    /\ LET ra == Rep(a)
           rb == Rep(b)
       IN  /\ ra /= rb   \* only merge distinct classes
           /\ IF rnk[ra] < rnk[rb]
              THEN /\ parent' = [parent EXCEPT ![ra] = rb]
                   /\ rnk'   = rnk
              ELSE IF rnk[ra] > rnk[rb]
              THEN /\ parent' = [parent EXCEPT ![rb] = ra]
                   /\ rnk'   = rnk
              ELSE \* equal rank: attach rb under ra, increment ra's rank
                   /\ parent' = [parent EXCEPT ![rb] = ra]
                   /\ rnk'   = [rnk EXCEPT ![ra] = rnk[ra] + 1]
    /\ ops_done' = ops_done + 1

Idle ==
    /\ ops_done >= MaxOps
    /\ UNCHANGED vars

Next ==
    \/ \E a \in Elements, b \in Elements : Union(a, b)
    \/ Idle

Spec == Init /\ [][Next]_vars

\* ---- Theorems (checked by TLC) --------------------------------------------

\* Spec => [](TypeInvariant /\ RepresentativeIdempotence /\ Symmetry /\
\* Transitivity /\ RankMonotonicity /\ RepresentativeRootedness): proved as
\* the conjunction of TypeSafety, RepresentativeIdempotenceSafety,
\* SymmetrySafety, TransitivitySafety, RankMonotonicitySafety, and
\* RepresentativeRootednessSafety in EquivalenceClass_Proof.tla.
====
