--------------------- MODULE ResourceRegistryDecomposed ---------------------
(* Negative decomposition witness for ResourceRegistry. Register atomically
   removes an existing key mapping and inserts the replacement. This model
   separates insertion from pruning; re-registering a key exposes both values
   between AddMapping and PruneOld and violates UniqueMapping. *)
EXTENDS Naturals, FiniteSets

CONSTANTS Keys, Values, NULL

VARIABLES entries, pkey, pval, pc

vars == <<entries, pkey, pval, pc>>

\* Each key maps to at most one value.
UniqueMapping ==
    \A k \in Keys :
        Cardinality({v \in Values : <<k, v>> \in entries}) <= 1

Init ==
    /\ entries = {}
    /\ pkey = NULL
    /\ pval = NULL
    /\ pc = "idle"

\* Insert the replacement before removing an existing value for the key.
AddMapping(k, v) ==
    /\ pc = "idle"
    /\ entries' = entries \cup {<<k, v>>}
    /\ pkey' = k
    /\ pval' = v
    /\ pc' = "pruning"

\* Remove other values for the in-flight key and restore uniqueness.
PruneOld ==
    /\ pc = "pruning"
    /\ entries' = { e \in entries : e[1] /= pkey \/ e[2] = pval }
    /\ pkey' = NULL
    /\ pval' = NULL
    /\ pc' = "idle"

Next ==
    \/ \E k \in Keys, v \in Values : AddMapping(k, v)
    \/ PruneOld

Spec == Init /\ [][Next]_vars
=============================================================================
