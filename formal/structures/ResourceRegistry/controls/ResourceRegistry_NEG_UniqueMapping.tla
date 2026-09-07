---- MODULE ResourceRegistry_NEG_UniqueMapping ----
\* Negative control for UniqueMapping.
\* Register adds a new pair without removing the previous mapping for the same
\* key. The isolated configuration must report UniqueMapping violated after
\* two different values are registered at that key.

EXTENDS Naturals, FiniteSets

CONSTANTS Keys, Values

VARIABLES entries

vars == <<entries>>

TypeInvariant ==
    entries \subseteq (Keys \X Values)

UniqueMapping ==
    \A k \in Keys :
        Cardinality({v \in Values : <<k, v>> \in entries}) <= 1

Init ==
    entries = {}

Register(k, v) ==
\* Fault: omit the old-key filter from the atomic upsert.
    /\ entries' = entries \cup {<<k, v>>}

Deregister(k) ==
    /\ \E v \in Values : <<k, v>> \in entries
    /\ entries' = {e \in entries : e[1] /= k}

Next ==
    \/ \E k \in Keys, v \in Values : Register(k, v)
    \/ \E k \in Keys : Deregister(k)

Spec == Init /\ [][Next]_vars

====
