---- MODULE ResourceRegistry ----
EXTENDS Naturals, FiniteSets

CONSTANTS Keys, Values

VARIABLES entries

vars == <<entries>>

\* entries represents a partial function from Keys to Values as a set of
\* <<key, value>> pairs with unique keys.

\* Every entry is a key-value pair. Register adds only values quantified from
\* the declared domains, Deregister only removes, and Init is empty. This is a
\* representation boundary rather than a separately controlled obligation.
TypeInvariant ==
    entries \subseteq (Keys \X Values)

\* Register is an atomic upsert: it removes every pair for k before adding one
\* replacement. The decomposition witness exposes the intermediate duplicate;
\* the negative control omits the filter at commit.
UniqueMapping ==
    \A k \in Keys :
        Cardinality({v \in Values : <<k, v>> \in entries}) <= 1

Init ==
    entries = {}

Register(k, v) ==
    \* Remove the previous mapping for k, then add its replacement.
    /\ entries' = {e \in entries : e[1] /= k} \cup {<<k, v>>}

Deregister(k) ==
    /\ \E v \in Values : <<k, v>> \in entries
    /\ entries' = {e \in entries : e[1] /= k}

Next ==
    \/ \E k \in Keys, v \in Values : Register(k, v)
    \/ \E k \in Keys : Deregister(k)

Spec == Init /\ [][Next]_vars

\* Spec => []UniqueMapping: proved as UniqueMappingSafety in ResourceRegistry_Proof.tla.
====
