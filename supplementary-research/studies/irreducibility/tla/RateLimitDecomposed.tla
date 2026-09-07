------------------------ MODULE RateLimitDecomposed -------------------------
(* Decomposition of rate limiter: separates check from increment.
   Concurrent acquire between CheckWindow/CheckCount and Increment causes
   count to exceed MaxPerWindow. TLC finds ThroughputInvariant violated.

   This unit is a count-only projection of canonical RateLimit: the window
   apparatus (the WindowDuration/MaxClock constants, the window_start/clock
   variables, Tick, TryAcquire's rollover-reset branch, and the
   WindowConsistency obligation) is not modeled.  That apparatus serves the
   obligation this one-target instrument does not check; the sole mechanism
   canonical uses to maintain ThroughputInvariant -- the fused
   count-test-and-increment of TryAcquire's else-branch -- is retained and
   defused as declared, so the reduction does not touch what the
   counterexample measures.  The multi-process apparatus (Procs, per-process
   pc/checked) supplies the concurrent acquire with an explicit second
   actor.                                                                    *)
EXTENDS Naturals

CONSTANT MaxPerWindow   \* e.g. 3
CONSTANT NULL

VARIABLE count, pc, checked

vars == <<count, pc, checked>>

Procs == {"p1", "p2"}

Init ==
    /\ count = 0
    /\ pc = [p \in Procs |-> "idle"]
    /\ checked = [p \in Procs |-> FALSE]

(* Step 1, reduced here to a pure phase advance: this module carries no
   window state (see the header), so unlike a CheckWindow that computes
   window_ok from clock/window_start, there is nothing here to check. *)
CheckWindow(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "check_count"]
    /\ UNCHANGED <<count, checked>>

(* Step 2: check if within window limit -- no mutation *)
CheckCount(p) ==
    /\ pc[p] = "check_count"
    /\ count < MaxPerWindow
    /\ checked' = [checked EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "checked"]
    /\ UNCHANGED count

(* Step 3: increment counter -- uses stale check *)
Increment(p) ==
    /\ pc[p] = "checked"
    /\ checked[p] = TRUE
    /\ count' = count + 1
    /\ checked' = [checked EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "idle"]

(* Concurrent acquire: another process acquires a slot atomically,
   consuming capacity that the first process already checked against *)
ConcurrentAcquire(p) ==
    /\ pc[p] = "idle"
    /\ count < MaxPerWindow
    /\ count' = count + 1
    /\ UNCHANGED <<pc, checked>>

Next ==
    \E p \in Procs :
        \/ CheckWindow(p)
        \/ CheckCount(p)
        \/ Increment(p)
        \/ ConcurrentAcquire(p)

ThroughputInvariant == count <= MaxPerWindow

Spec == Init /\ [][Next]_vars
=============================================================================
