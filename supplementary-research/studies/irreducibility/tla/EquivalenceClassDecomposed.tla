--------------------- MODULE EquivalenceClassDecomposed ---------------------
(* Decomposition of the equivalence-class / union-find algorithmic primitive.

   Canonical EquivalenceClass maintains its forest invariants because Union
   reads the two representatives (and their ranks) and COMMITS the parent link
   (+ rank bump) in one ATOMIC step, so the parent graph stays acyclic.  This
   decomposition splits the root/rank read from the link commit: BeginUnion
   reads the roots and stages the decided link, CommitLink applies it.  Two
   unions on the same pair can both read the pair as roots (before either
   commits) and then both commit opposite links -- parent[x]=y AND parent[y]=x,
   a CYCLE -- so Rep(e) is no longer a parent fixed point and PathConsistency
   breaks.

   Target invariant: `PathConsistency` (canonical EquivalenceClass .cfg).
   On `Transitivity`: the canonical Transitivity ==
   (Rep(a)=Rep(b) /\ Rep(b)=Rep(c)) => Rep(a)=Rep(c) is over the TOTAL function
   Rep, so it is a tautology (transitivity of value equality) and cannot be
   violated by any state.  PathConsistency is therefore the breakable target of
   the two.  TLC finds PathConsistency violated once the cycle is committed.    *)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Elements, MaxOps, NULL

VARIABLES parent, rnk, ops_done, staged

vars == <<parent, rnk, ops_done, staged>>

\* Rep: root of e under parent[] (same function-fixpoint form as the canonical
\* spec; budget MaxOps + 1 steps).  Under a cycle this returns a non-root value.
RepFun[k \in 0..(MaxOps + 1)] ==
    IF k = 0 THEN [e \in Elements |-> e]
    ELSE [e \in Elements |-> IF parent[e] = e THEN e
                             ELSE RepFun[k - 1][parent[e]]]

Rep(e) == RepFun[MaxOps + 1][e]

\* Canonical invariant: each element's representative is a parent fixed point,
\* that is, a root.  A cycle in parent makes this false.
PathConsistency ==
    \A e \in Elements : parent[Rep(e)] = Rep(e)

Init ==
    /\ parent = [e \in Elements |-> e]
    /\ rnk = [e \in Elements |-> 0]
    /\ ops_done = 0
    /\ staged = {}

\* Step 1: read the two roots and their ranks and STAGE the decided link
\* (and, for the equal-rank case, the root to bump) -- WITHOUT committing parent.
\* The canonical Union commits the parent link in this same step.
BeginUnion(a, b) ==
    /\ ops_done < MaxOps
    /\ LET ra == Rep(a)
           rb == Rep(b)
       IN  /\ ra /= rb
           /\ LET entry ==
                    IF rnk[ra] < rnk[rb]
                    THEN [from |-> ra, to |-> rb, bump |-> NULL]
                    ELSE IF rnk[ra] > rnk[rb]
                    THEN [from |-> rb, to |-> ra, bump |-> NULL]
                    ELSE [from |-> rb, to |-> ra, bump |-> ra]
              IN staged' = staged \cup {entry}
    /\ ops_done' = ops_done + 1
    /\ UNCHANGED <<parent, rnk>>

\* Step 2: commit a staged link.  It uses the root read at BeginUnion time, which
\* a concurrently-committed link may have invalidated.
CommitLink(entry) ==
    /\ entry \in staged
    /\ parent' = [parent EXCEPT ![entry.from] = entry.to]
    /\ rnk' = IF entry.bump = NULL
              THEN rnk
              ELSE [rnk EXCEPT ![entry.bump] = rnk[entry.bump] + 1]
    /\ staged' = staged \ {entry}
    /\ UNCHANGED ops_done

Next ==
    \/ \E a \in Elements, b \in Elements : BeginUnion(a, b)
    \/ \E entry \in staged : CommitLink(entry)

Spec == Init /\ [][Next]_vars
=============================================================================
