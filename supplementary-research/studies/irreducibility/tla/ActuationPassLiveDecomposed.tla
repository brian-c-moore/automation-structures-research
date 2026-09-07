----------------------- MODULE ActuationPassLiveDecomposed -----------------------
(* Irreducibility-by-construction for the concept-faithful ActuationPassLive.

   This module is ActuationPassLive with EXACTLY ONE change: the fused
   read-and-apply step of `Actuate` is split into ReadAllocation (cache the
   seat's allocation) and ApplyFromCache (write the effect from the cache).
   Nothing else is weakened -- the environment's withdrawal guard, the
   closure step, the constants and the invariants are the base module's.

   The split runs against the enriched model, which carries a live allocation
   environment: the base ActuationPass.tla freezes `allocation`, so the
   concurrent deallocate cannot occur there at all.

   TLC must find a violation: a seat is allocated, its allocation is cached,
   the environment deallocates it
   (permitted -- the effect has not been applied yet, so the seat is not
   inside the pass's snapshot boundary), then ApplyFromCache applies the
   operation to the stale resource. EffectFidelity and ActuationScope both
   break, on a seat that no longer holds an allocation.                       *)
EXTENDS FiniteSets

CONSTANTS Seats, Resources, NULL

VARIABLES allocation, effects, complete,
          cached        \* the split-out read: cached[s] /= NULL means a read
                        \* for seat s is in flight and not yet applied

vars == <<allocation, effects, complete, cached>>

Actuated == {s \in Seats : effects[s] /= NULL}

TypeInvariant ==
    /\ allocation \in [Seats -> Resources \cup {NULL}]
    /\ effects    \in [Seats -> Resources \cup {NULL}]
    /\ complete   \in BOOLEAN
    /\ cached     \in [Seats -> Resources \cup {NULL}]

ActuationScope ==
    \A s \in Actuated : allocation[s] /= NULL

EffectFidelity ==
    \A s \in Seats : effects[s] /= NULL => effects[s] = allocation[s]

PassCompleteness ==
    complete => \A s \in Seats : allocation[s] /= NULL => effects[s] /= NULL

Init ==
    /\ allocation \in [Seats -> Resources \cup {NULL}]
    /\ effects = [s \in Seats |-> NULL]
    /\ complete = FALSE
    /\ cached = [s \in Seats |-> NULL]

(* THE SPLIT -- step 1: read the allocation into a cache. *)
ReadAllocation(s) ==
    /\ ~complete
    /\ effects[s] = NULL
    /\ cached[s] = NULL
    /\ allocation[s] /= NULL
    /\ cached' = [cached EXCEPT ![s] = allocation[s]]
    /\ UNCHANGED <<allocation, effects, complete>>

(* THE SPLIT -- step 2: apply the operation from the cached read. *)
ApplyFromCache(s) ==
    /\ ~complete
    /\ cached[s] /= NULL
    /\ effects[s] = NULL
    /\ effects' = [effects EXCEPT ![s] = cached[s]]
    /\ cached'  = [cached EXCEPT ![s] = NULL]
    /\ UNCHANGED <<allocation, complete>>

(* The environment, unchanged from the base module. *)
Allocate(s, r) ==
    /\ ~complete
    /\ allocation[s] = NULL
    /\ allocation' = [allocation EXCEPT ![s] = r]
    /\ UNCHANGED <<effects, complete, cached>>

Deallocate(s) ==
    /\ ~complete
    /\ allocation[s] /= NULL
    /\ effects[s] = NULL
    /\ allocation' = [allocation EXCEPT ![s] = NULL]
    /\ UNCHANGED <<effects, complete, cached>>

Finish ==
    /\ ~complete
    /\ \A s \in Seats : allocation[s] /= NULL => effects[s] /= NULL
    /\ complete' = TRUE
    /\ UNCHANGED <<allocation, effects, cached>>

Next ==
    \/ \E s \in Seats : ReadAllocation(s)
    \/ \E s \in Seats : ApplyFromCache(s)
    \/ \E s \in Seats, r \in Resources : Allocate(s, r)
    \/ \E s \in Seats : Deallocate(s)
    \/ Finish

Spec == Init /\ [][Next]_vars

\* TLC finds a violation of EffectFidelity (and of ActuationScope).
=============================================================================
