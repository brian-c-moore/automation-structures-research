------------------------- MODULE SamplerDecomposed --------------------------
(* Decomposition of sampler: separates distribution read from draw.
   A concurrent zero between ReadDistribution and DrawFromCache causes
   selection of an item with zero probability.
   TLC finds SupportConsistency violated.

   Differences from Sampler.tla besides the split:
     - Sampler defines TypeInvariant, BoundedSample and SupportConsistency and
       Sampler.cfg checks all three; this defines SupportConsistency alone.
     - SupportConsistency here is `drawn # NULL => probs[drawn] > 0`, over one
       drawn item; Sampler's quantifies over the selected set.
     - The state is a single `drawn` item; Sampler carries `selected`, a subset
       of Items.  Sampler's BoundedSample bounds Cardinality(selected) and is
       not statable here; SampleSize is not declared.
     - `Items` is a literal set of three here; Sampler declares it a CONSTANT
       bound to four by Sampler.cfg.
     - `Reset` corresponds to no Sampler action.
     - Init sets every probability to 1.  Sampler's Init draws `distribution`
       over [Items -> 0..MaxProb], so an item outside the support is present
       from the start; here one arises only from ConcurrentZero.  CONSTANT
       MaxProb is declared and read at no line.
     - ConcurrentZero has no counterpart in Sampler, whose only action is
       Sample and which carries UNCHANGED distribution.  It is guarded by
       pc = "cached", set only by ReadDistribution and also required by
       DrawFromCache.                                                         *)
EXTENDS Naturals, FiniteSets

CONSTANT MaxProb   \* e.g. 3
CONSTANT NULL

VARIABLE probs, cached_probs, drawn, pc

vars == <<probs, cached_probs, drawn, pc>>

Items == {"i1", "i2", "i3"}

Init ==
    /\ probs = [i \in Items |-> 1]        \* all items have positive probability
    /\ cached_probs = [i \in Items |-> 0]
    /\ drawn = NULL
    /\ pc = "idle"

(* Step 1: cache the current distribution *)
ReadDistribution ==
    /\ pc = "idle"
    /\ cached_probs' = probs
    /\ pc' = "cached"
    /\ UNCHANGED <<probs, drawn>>

(* Step 2: draw from cached distribution — pick an item with positive cached prob *)
DrawFromCache ==
    /\ pc = "cached"
    /\ \E i \in Items :
        /\ cached_probs[i] > 0
        /\ drawn' = i
    /\ pc' = "drawn"
    /\ UNCHANGED <<probs, cached_probs>>

(* Concurrent: environment zeros out an item's probability *)
ConcurrentZero ==
    /\ pc = "cached"
    /\ \E i \in Items :
        /\ probs' = [probs EXCEPT ![i] = 0]
    /\ UNCHANGED <<cached_probs, drawn, pc>>

(* Reset *)
Reset ==
    /\ pc = "drawn"
    /\ pc' = "idle"
    /\ drawn' = NULL
    /\ UNCHANGED <<probs, cached_probs>>

Next ==
    \/ ReadDistribution
    \/ DrawFromCache
    \/ ConcurrentZero
    \/ Reset

(* Selected item must have positive probability in current distribution *)
SupportConsistency ==
    drawn # NULL => probs[drawn] > 0

Spec == Init /\ [][Next]_vars
=============================================================================
