---- MODULE Sampler_NEG_SupportConsistency ----
\* NEGATIVE CONTROL, generated. Not a specification: this is Sampler
\* carrying one deliberate defect, so that a checker fails on it.
\*
\*   base module      : Sampler
\*   mutation site    : Sample
\*   target           : SupportConsistency
\*   required outcome : with only SupportConsistency declared, TLC MUST report the invariant
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

Sample ==
    /\ Cardinality(selected) < SampleSize
    /\ \E i \in Items :
\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
        /\ selected' = selected \cup {i}
\* ---- MUTATION ENDS.
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
