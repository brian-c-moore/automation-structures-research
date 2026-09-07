----------------------- MODULE ActuationPassDecomposed -----------------------
(* Decomposition of actuation pass: separates allocation read from action.
   A concurrent deallocate between ReadAllocation and ActuateFromCache
   causes actuation on a deallocated seat.
   TLC finds ActuationScope violated.

   This module is not ActuationPass-minus-one-mechanism. It diverges from the
   canonical module as follows:
   - the allocation is re-encoded from canonical's function
     [Seats -> Resources \cup {NULL}] to a SET of allocated seats, dropping
     `side_effects` and `Resources` entirely; ActuationScope below is the
     subset form of canonical's quantified predicate under the projection
     allocated = {s : allocation[s] /= NULL};
   - the invariant list does not match canonical's.  Canonical defines
     TypeInvariant and ActuationScope; this defines ActuationScope alone.
     TypeInvariant is unstatable here -- it types `allocation` as a function
     into Resources \cup {NULL} and types `side_effects`, and the re-encoding
     above leaves neither in this model;
   - Seats is a local literal set (the .cfg cannot set the model's scope)
     and CONSTANT NULL is declared but never used;
   - ActuateFromCache drops canonical Actuate's `s \notin actuated` dedup
     guard; `Reset` recycles the pass and corresponds to no canonical
     ActuationPass action; Init pins `allocated = Seats` where canonical
     draws the allocation freely.
   Both cold passes fire ActuationScope through the read/deallocate/actuate
   window, and no violation route bypasses the split (ConcurrentDeallocate
   alone cannot break the subset predicate from actuated = {}).  The
   counterexample against the concept carrier, at canonical-cfg parity, is
   irreducibility/ActuationPassLiveDecomposed.                              *)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NULL

VARIABLE allocated, cached_alloc, actuated, pc

vars == <<allocated, cached_alloc, actuated, pc>>

Seats == {"s1", "s2", "s3"}

Init ==
    /\ allocated = Seats          \* all seats start allocated
    /\ cached_alloc = {}
    /\ actuated = {}
    /\ pc = "idle"

(* Step 1: read current allocations into cache *)
ReadAllocation ==
    /\ pc = "idle"
    /\ cached_alloc' = allocated
    /\ pc' = "cached"
    /\ UNCHANGED <<allocated, actuated>>

(* Step 2: actuate from cached allocation *)
ActuateFromCache ==
    /\ pc = "cached"
    /\ \E s \in cached_alloc :
        /\ actuated' = actuated \cup {s}
    /\ pc' = "done"
    /\ UNCHANGED <<allocated, cached_alloc>>

(* Concurrent: environment deallocates a seat between read and actuate *)
ConcurrentDeallocate ==
    /\ pc = "cached"
    /\ \E s \in allocated :
        /\ allocated' = allocated \ {s}
    /\ UNCHANGED <<cached_alloc, actuated, pc>>

(* Reset *)
Reset ==
    /\ pc = "done"
    /\ pc' = "idle"
    /\ actuated' = {}
    /\ UNCHANGED <<allocated, cached_alloc>>

Next ==
    \/ ReadAllocation
    \/ ActuateFromCache
    \/ ConcurrentDeallocate
    \/ Reset

(* Every actuated seat must currently be allocated *)
ActuationScope ==
    actuated \subseteq allocated

Spec == Init /\ [][Next]_vars
=============================================================================
