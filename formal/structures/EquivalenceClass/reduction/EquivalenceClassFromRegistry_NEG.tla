---- MODULE EquivalenceClassFromRegistry_NEG ----
\* Negative control for ECRefinement. UnionStep updates the parent and rank
\* registries without charging the Budget allocation. Component invariants
\* remain valid, but the mapped parent changes while mapped ops_done is fixed;
\* no EquivalenceClass Union, Idle, or stutter step has that effect. TLC must
\* therefore report ECRefinement violated.

EXTENDS Naturals, FiniteSets

CONSTANTS Elements, MaxOps

VARIABLES p_entries, r_entries,
          b_capacity, b_allocated, b_reserved, b_pending

vars == <<p_entries, r_entries,
          b_capacity, b_allocated, b_reserved, b_pending>>

RankValues == 0..MaxOps

PReg == INSTANCE ResourceRegistry WITH Keys <- Elements,
                                       Values <- Elements,
                                       entries <- p_entries
RReg == INSTANCE ResourceRegistry WITH Keys <- Elements,
                                       Values <- RankValues,
                                       entries <- r_entries
Bgt == INSTANCE Budget WITH Capacity <- MaxOps,
                            capacity <- b_capacity,
                            allocated <- b_allocated,
                            reserved <- b_reserved,
                            pending_eviction <- b_pending

ParentUnique == PReg!UniqueMapping
RankUnique == RReg!UniqueMapping
BudgetSafety == Bgt!SafetyInvariant

MapParent ==
    [e \in Elements |->
        IF \E v \in Elements : <<e, v>> \in p_entries
        THEN CHOOSE v \in Elements : <<e, v>> \in p_entries
        ELSE e]

MapRnk ==
    [e \in Elements |->
        IF \E v \in RankValues : <<e, v>> \in r_entries
        THEN CHOOSE v \in RankValues : <<e, v>> \in r_entries
        ELSE 0]

RepFunC[k \in 0..(MaxOps + 1)] ==
    IF k = 0 THEN [e \in Elements |-> e]
    ELSE [e \in Elements |-> IF MapParent[e] = e THEN e
                             ELSE RepFunC[k - 1][MapParent[e]]]

RepC(e) == RepFunC[MaxOps + 1][e]

Upsert(S, k, v) == {e \in S : e[1] /= k} \cup {<<k, v>>}

TypeInvariant ==
    /\ p_entries \subseteq (Elements \X Elements)
    /\ r_entries \subseteq (Elements \X RankValues)
    /\ b_capacity = MaxOps
    /\ b_allocated \in 0..MaxOps
    /\ b_reserved = 0
    /\ b_pending = 0

Init ==
    /\ p_entries = {}
    /\ r_entries = {}
    /\ b_capacity = MaxOps
    /\ b_allocated = 0
    /\ b_reserved = 0
    /\ b_pending = 0

\* Fault: omit the Budget charge while retaining the registry updates.
UnionStep(a, b) ==
    /\ b_allocated + b_reserved + b_pending + 1 <= b_capacity
    /\ LET ra == RepC(a)
           rb == RepC(b)
       IN  /\ ra /= rb
           /\ IF MapRnk[ra] < MapRnk[rb]
              THEN /\ p_entries' = Upsert(p_entries, ra, rb)
                   /\ r_entries' = r_entries
              ELSE IF MapRnk[ra] > MapRnk[rb]
              THEN /\ p_entries' = Upsert(p_entries, rb, ra)
                   /\ r_entries' = r_entries
              ELSE /\ p_entries' = Upsert(p_entries, rb, ra)
                   /\ r_entries' = Upsert(r_entries, ra, MapRnk[ra] + 1)
    /\ UNCHANGED <<b_capacity, b_allocated, b_reserved, b_pending>>

Idle ==
    /\ b_allocated >= b_capacity
    /\ UNCHANGED vars

Next ==
    \/ \E a \in Elements, b \in Elements : UnionStep(a, b)
    \/ Idle

Spec == Init /\ [][Next]_vars

EC == INSTANCE EquivalenceClass WITH
        parent   <- MapParent,
        rnk      <- MapRnk,
        ops_done <- b_allocated,
        Elements <- Elements,
        MaxOps   <- MaxOps

ECRefinement == EC!Spec

\* The paired configuration declares only ECRefinement as the property target.
====
