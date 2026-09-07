---- MODULE SamplerImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for Sampler. distribution maps indexwise and the *)
(* distinct selected Vec maps to a set. The finite MaxProb bound is an      *)
(* explicit library-instance premise; the Rust constructor itself accepts  *)
(* the wider u64 domain. Draw-rule frequency claims remain outside.         *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, FiniteSets

CONSTANTS NumItems, SampleSize, MaxProb
ASSUME ItemCountType == NumItems \in Nat /\ NumItems >= 2
ASSUME SampleSizeType == SampleSize \in Nat /\ SampleSize >= 2
ASSUME MaxProbType == MaxProb \in Nat /\ MaxProb >= 1
Items == 0..(NumItems - 1)

VARIABLES num_items, sample_size, distribution, selected
vars == <<num_items, sample_size, distribution, selected>>

S == INSTANCE Sampler WITH
        Items <- Items,
        SampleSize <- SampleSize,
        MaxProb <- MaxProb,
        distribution <- distribution,
        selected <- selected

ImplInvariant ==
    /\ num_items = NumItems
    /\ sample_size = SampleSize
    /\ S!TypeInvariant
    /\ S!BoundedSample
    /\ S!SupportConsistency

Init ==
    /\ num_items = NumItems
    /\ sample_size = SampleSize
    /\ distribution \in [Items -> 0..MaxProb]
    /\ selected = {}
    /\ ImplInvariant

ImplSample(i) ==
    /\ ImplInvariant
    /\ i \in Items
    /\ S!Cardinality(selected) < SampleSize
    /\ distribution[i] > 0
    /\ i \notin selected
    /\ selected' = selected \cup {i}
    /\ UNCHANGED <<num_items, sample_size, distribution>>
    /\ ImplInvariant'

ImplZero(i) ==
    /\ ImplInvariant
    /\ i \in Items
    /\ i \notin selected
    /\ distribution' = [distribution EXCEPT ![i] = 0]
    /\ UNCHANGED <<num_items, sample_size, selected>>
    /\ ImplInvariant'

ImplReadOrReject == UNCHANGED vars
ImplNext ==
    \/ \E i \in Items : ImplSample(i)
    \/ \E i \in Items : ImplZero(i)
    \/ ImplReadOrReject
Spec == Init /\ [][ImplNext]_vars

Refinement == S!Spec
====
