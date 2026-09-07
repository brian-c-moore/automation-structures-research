------------------------- MODULE SamplerLiveDecomposed ----------------------
(* Irreducibility-by-construction for the concept-faithful SamplerLive.

   This module is SamplerLive with EXACTLY ONE change: the fused
   read-and-draw step of `Sample` is split into ReadDistribution (cache the
   distribution) and DrawFromCache (pick an item whose CACHED probability is
   positive). Nothing else is weakened -- the writer's ownership guard, the
   constants and the invariants are the base module's, verbatim.

   The split runs against the enriched model, which carries a live
   distribution writer. The pinned Sampler.tla freezes `distribution`, so the
   concurrent zero cannot occur there at all, which is why the corpus's other
   instrument, irreducibility/SamplerDecomposed, carries its own private
   ConcurrentZero writer rather than decomposing the canonical module. That
   instrument is the pinned entry's evidence; this one is a decomposition of
   the module it names.

   TLC must find a violation: the distribution is cached; an item's
   probability drops to zero (permitted -- the item has not been drawn, so it
   is not inside the completed draw); DrawFromCache selects it on the
   strength of the stale cache. A zero-probability item is in the selected
   set. BoundedSample still holds there, which is why the two obligations are
   stated separately.                                                      *)
EXTENDS Naturals, FiniteSets

CONSTANTS Items, SampleSize, MaxProb

VARIABLES distribution, selected,
          cached,       \* the split-out read: the cached distribution
          phase         \* "idle" = no read in flight; "read" = one is

vars == <<distribution, selected, cached, phase>>

TypeInvariant ==
    /\ distribution \in [Items -> 0..MaxProb]
    /\ selected \subseteq Items
    /\ cached \in [Items -> 0..MaxProb]
    /\ phase \in {"idle", "read"}

BoundedSample ==
    Cardinality(selected) <= SampleSize

SupportConsistency ==
    \A s \in selected : distribution[s] > 0

Init ==
    /\ distribution \in [Items -> 0..MaxProb]
    /\ selected = {}
    /\ cached = [i \in Items |-> 0]
    /\ phase = "idle"

(* THE SPLIT -- step 1: read the distribution into a cache. *)
ReadDistribution ==
    /\ phase = "idle"
    /\ Cardinality(selected) < SampleSize
    /\ cached' = distribution
    /\ phase' = "read"
    /\ UNCHANGED <<distribution, selected>>

(* THE SPLIT -- step 2: draw from the cached distribution. *)
DrawFromCache ==
    /\ phase = "read"
    /\ \E i \in Items :
        /\ cached[i] > 0
        /\ selected' = selected \cup {i}
    /\ phase' = "idle"
    /\ UNCHANGED <<distribution, cached>>

(* The environment, unchanged from the base module. *)
Zero(i) ==
    /\ i \notin selected
    /\ distribution' = [distribution EXCEPT ![i] = 0]
    /\ UNCHANGED <<selected, cached, phase>>

Next ==
    \/ ReadDistribution
    \/ DrawFromCache
    \/ \E i \in Items : Zero(i)

Spec == Init /\ [][Next]_vars

\* TLC finds a violation of SupportConsistency.
=============================================================================
