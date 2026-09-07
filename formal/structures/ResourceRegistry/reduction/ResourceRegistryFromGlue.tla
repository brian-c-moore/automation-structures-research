---- MODULE ResourceRegistryFromGlue ----
\* State-only re-encoding of ResourceRegistry. `store` is the retained pair-set
\* buffer; no component state is present. Total-function write-once stores do
\* not implement Register upsert and Deregister.
\*
\* UniqueMapping is representation-relative: a total-function encoding makes
\* duplicate values for one key unrepresentable, whereas this pair-set carrier
\* exposes the split-upsert counterexample. MappedUniqueMapping is stated and
\* checked directly over store. Refinement is a variable relabeling; no other
\* component supplies the obligation.
EXTENDS Naturals, FiniteSets

CONSTANTS Keys, Values

\* Pair-set buffer; no component state.
VARIABLES store

vars == <<store>>

TypeInvariant ==
    store \subseteq (Keys \X Values)

\* The target obligation restated over the construction state.
MappedUniqueMapping ==
    \A k \in Keys :
        Cardinality({v \in Values : <<k, v>> \in store}) <= 1

Init ==
    store = {}

\* ResourceRegistry's own actions, carried verbatim.
Register(k, v) ==
    store' = {e \in store : e[1] /= k} \cup {<<k, v>>}

Deregister(k) ==
    /\ \E v \in Values : <<k, v>> \in store
    /\ store' = {e \in store : e[1] /= k}

Next ==
    \/ \E k \in Keys, v \in Values : Register(k, v)
    \/ \E k \in Keys : Deregister(k)

Spec == Init /\ [][Next]_vars

\* --- Refinement mapping to ResourceRegistry ---
RR == INSTANCE ResourceRegistry WITH
        entries <- store,
        Keys    <- Keys,
        Values  <- Values

ResourceRegistryRefinement == RR!Spec
====
