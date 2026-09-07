---- MODULE Sampler ----
(* Bounded support-preserving selection with a mutable distribution.

   `Sample` reads the support and commits the selected item in one transition.
   `Zero` is the environment writer that can remove an unselected item from
   the support. It may not invalidate an item already selected, because that
   item is inside the completed draw's ownership boundary.

   The advertised obligations are `BoundedSample` and `SupportConsistency`.
   They do not determine a probability law: weighted and uniform generators
   can both satisfy this acceptor specification. Frequency claims therefore
   belong to a separately stated draw rule and empirical test, not this model.
   The carrier also makes no exactly-once or coverage claim.                *)
EXTENDS Naturals, FiniteSets

CONSTANTS Items, SampleSize, MaxProb

VARIABLES distribution, selected

vars == <<distribution, selected>>

TypeInvariant ==
    /\ distribution \in [Items -> 0..MaxProb]
    /\ selected \subseteq Items

\* The selected set stays within the declared sample-size bound.
BoundedSample ==
    Cardinality(selected) <= SampleSize

\* Selected items remain in the support of the mutable distribution.
SupportConsistency ==
    \A s \in selected : distribution[s] > 0

Init ==
    /\ distribution \in [Items -> 0..MaxProb]  \* full type range: an item may have probability 0 (outside the support), so Sample's distribution[i] > 0 guard is load-bearing
    /\ selected = {}

\* The draw: the distribution read and the
\* selection commit in one step. Splitting them is exactly
\* SamplerDecomposed.
Sample ==
    /\ Cardinality(selected) < SampleSize
    /\ \E i \in Items :
        /\ distribution[i] > 0
        /\ selected' = selected \cup {i}
        /\ UNCHANGED distribution

\* The environment writer: an item's
\* probability drops to zero -- "removed from dataset, belief deregistered".
\* Guarded by the draw's ownership of what it has already selected (see the
\* header): an already-drawn item is inside the completed operation, so
\* withdrawing its weight is not the read/draw race modeled by the control.
Zero(i) ==
    /\ i \notin selected
    /\ distribution' = [distribution EXCEPT ![i] = 0]
    /\ UNCHANGED selected

Next ==
    \/ Sample
    \/ \E i \in Items : Zero(i)

Spec == Init /\ [][Next]_vars

\* Spec => [](TypeInvariant /\ BoundedSample /\ SupportConsistency) is proved
\* in Sampler_Proof.tla.
====
