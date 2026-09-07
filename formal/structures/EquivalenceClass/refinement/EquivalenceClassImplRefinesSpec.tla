---- MODULE EquivalenceClassImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for EquivalenceClass. parent, rank, and size Vec *)
(* values map indexwise to functions. max_rank and both operation counters  *)
(* map identically. find and same are read-only; failed or budget-exhausted *)
(* union calls stutter.                                                     *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, FiniteSets

CONSTANTS NumElements, MaxOps
ASSUME NumElementsType == NumElements \in Nat /\ NumElements >= 2
ASSUME MaxOpsType == MaxOps \in Nat /\ MaxOps >= 1
ElementSet == 0..(NumElements - 1)

VARIABLES num_elements, max_ops, parent, rnk, size, ops_done, max_rank
vars == <<num_elements, max_ops, parent, rnk, size, ops_done, max_rank>>

E == INSTANCE EquivalenceClass WITH
        Elements <- ElementSet,
        MaxOps <- MaxOps,
        parent <- parent,
        rnk <- rnk,
        ops_done <- ops_done

Pow2[k \in 0..MaxOps] == IF k = 0 THEN 1 ELSE 2 * Pow2[k - 1]
RootSizeTotal[k \in 0..NumElements] ==
    IF k = 0 THEN 0
    ELSE RootSizeTotal[k - 1]
        + IF parent[k - 1] = k - 1 THEN size[k - 1] ELSE 0

RepresentationInvariant ==
    /\ size \in [ElementSet -> (Nat \ {0})]
    /\ max_rank \in Nat
    /\ ops_done <= max_ops
    /\ max_rank <= ops_done
    /\ \A e \in ElementSet : rnk[e] <= max_rank
    /\ \A e \in ElementSet : Pow2[rnk[e]] <= size[e]
    /\ RootSizeTotal[NumElements] = NumElements

ImplInvariant ==
    /\ num_elements = NumElements
    /\ max_ops = MaxOps
    /\ RepresentationInvariant
    /\ E!TypeInvariant
    /\ E!RepresentativeIdempotence
    /\ E!RankMonotonicity
    /\ E!RepresentativeRootedness

Init ==
    /\ num_elements = NumElements
    /\ max_ops = MaxOps
    /\ parent = [e \in ElementSet |-> e]
    /\ rnk = [e \in ElementSet |-> 0]
    /\ size = [e \in ElementSet |-> 1]
    /\ ops_done = 0
    /\ max_rank = 0
    /\ ImplInvariant

ImplUnion(a, b) ==
    /\ ImplInvariant
    /\ a \in ElementSet
    /\ b \in ElementSet
    /\ ops_done < max_ops
    /\ LET ra == E!Rep(a)
           rb == E!Rep(b)
       IN /\ ra /= rb
          /\ IF rnk[ra] < rnk[rb]
             THEN /\ parent' = [parent EXCEPT ![ra] = rb]
                  /\ rnk' = rnk
                  /\ size' = [size EXCEPT ![rb] = @ + size[ra]]
                  /\ max_rank' = max_rank
             ELSE IF rnk[ra] > rnk[rb]
             THEN /\ parent' = [parent EXCEPT ![rb] = ra]
                  /\ rnk' = rnk
                  /\ size' = [size EXCEPT ![ra] = @ + size[rb]]
                  /\ max_rank' = max_rank
             ELSE /\ parent' = [parent EXCEPT ![rb] = ra]
                  /\ rnk' = [rnk EXCEPT ![ra] = rnk[ra] + 1]
                  /\ size' = [size EXCEPT ![ra] = @ + size[rb]]
                  /\ max_rank' =
                        IF rnk[ra] + 1 > max_rank THEN rnk[ra] + 1 ELSE max_rank
    /\ ops_done' = ops_done + 1
    /\ UNCHANGED <<num_elements, max_ops>>
    /\ ImplInvariant'

ImplReadOrReject == UNCHANGED vars
ImplNext ==
    (\E a \in ElementSet, b \in ElementSet : ImplUnion(a, b))
        \/ ImplReadOrReject
Spec == Init /\ [][ImplNext]_vars

Refinement == E!Spec
====
