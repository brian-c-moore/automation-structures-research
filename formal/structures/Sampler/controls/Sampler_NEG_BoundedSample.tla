---- MODULE Sampler_NEG_BoundedSample ----
\* NEGATIVE CONTROL, generated. Not a specification: this is Sampler
\* carrying one deliberate defect, so that a checker fails on it.
\*
\*   base module      : Sampler
\*   mutation site    : Sample
\*   target           : BoundedSample
\*   required outcome : with only BoundedSample declared, TLC MUST report the invariant
\*                      violated. A run that finds no error is a control that has
\*                      stopped measuring.
\*
\* The mutation is delimited by the markers below. Outside them, and
\* apart from the module name, this file is Sampler verbatim, less
\* that module's commentary.

EXTENDS Naturals, FiniteSets

CONSTANTS Items, SampleSize, MaxProb

VARIABLES distribution, selected

vars == <<distribution, selected>>

TypeInvariant ==
    /\ distribution \in [Items -> 0..MaxProb]
    /\ selected \subseteq Items

BoundedSample ==
    Cardinality(selected) <= SampleSize

SupportConsistency ==
    \A s \in selected : distribution[s] > 0

Init ==
    /\ distribution \in [Items -> 0..MaxProb]
    /\ selected = {}

\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
Sample ==
    /\ TRUE
\* ---- MUTATION ENDS.
    /\ \E i \in Items :
        /\ distribution[i] > 0
        /\ selected' = selected \cup {i}
        /\ UNCHANGED distribution

Zero(i) ==
    /\ i \notin selected
    /\ distribution' = [distribution EXCEPT ![i] = 0]
    /\ UNCHANGED selected

Next ==
    \/ Sample
    \/ \E i \in Items : Zero(i)

Spec == Init /\ [][Next]_vars

====
