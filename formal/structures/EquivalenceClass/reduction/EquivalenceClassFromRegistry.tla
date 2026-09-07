---- MODULE EquivalenceClassFromRegistry ----
\* Refinement construction for EquivalenceClass. One ResourceRegistry stores
\* non-identity parent links, a second stores nonzero rank values, and Budget
\* stores the successful-union count. Missing parent and rank entries map to
\* identity and zero. MapParent, MapRnk, and RepC are derived views; no extra
\* state is retained.
\*
\* UnionStep atomically computes both representatives, performs the
\* union-by-rank upserts, and charges one Budget allocation. The construction
\* proves expressibility under that atomic-step contract; it does not claim a
\* distributed or non-atomic implementation refinement.

EXTENDS Naturals, FiniteSets

CONSTANTS Elements, MaxOps

\* Parent-registry entries + rank-registry entries + Budget component
\* state. No glue variables.
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

\* Component invariants retained by the construction.
ParentUnique == PReg!UniqueMapping
RankUnique == RReg!UniqueMapping
BudgetSafety == Bgt!SafetyInvariant

\* --- Defaulted views over registry state ---------------------------------
\* An unregistered key defaults: parent to the key itself (its own root),
\* rank to 0. These are the constructions' entire read surface.
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

\* The representative fold over the defaulted parent view -- the same
\* derivation the target defines over its parent array.
RepFunC[k \in 0..(MaxOps + 1)] ==
    IF k = 0 THEN [e \in Elements |-> e]
    ELSE [e \in Elements |-> IF MapParent[e] = e THEN e
                             ELSE RepFunC[k - 1][MapParent[e]]]

RepC(e) == RepFunC[MaxOps + 1][e]

\* RR!Register's effect, verbatim (the upsert).
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

\* Fused successful union: budget guard and charge, representative lookup,
\* and the two registry updates occur in one transition.
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
    /\ b_allocated' = b_allocated + 1
    /\ UNCHANGED <<b_capacity, b_reserved, b_pending>>

Idle ==
    /\ b_allocated >= b_capacity
    /\ UNCHANGED vars

Next ==
    \/ \E a \in Elements, b \in Elements : UnionStep(a, b)
    \/ Idle

Spec == Init /\ [][Next]_vars

\* --- Refinement mapping to EquivalenceClass ---
\* Both stores map through their defaulted views; the operation count maps to
\* the Budget allocation.
EC == INSTANCE EquivalenceClass WITH
        parent   <- MapParent,
        rnk      <- MapRnk,
        ops_done <- b_allocated,
        Elements <- Elements,
        MaxOps   <- MaxOps

\* Every construction behavior satisfying this property is an
\* EquivalenceClass behavior under the mapping above.
ECRefinement == EC!Spec

\* Spec => ECRefinement: TLC-checked as PROPERTY ECRefinement (this
\* module's .cfg, bounded); TLAPS lift discharged unbounded in
\* EquivalenceClassFromRegistry_Proof.tla. Run-specific counts and tool output
\* are external to this module, so this source states only the proved relation.
\* The proof reuses the EquivalenceClass_Proof RepFun idioms,
\* CHOOSE-determinacy over UniqueMapping, and the registry-to-function
\* Upsert/EXCEPT bridge.
====
