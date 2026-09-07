-------------------------- MODULE SignalDecomposed --------------------------
(* Decomposition of signal.

   Canonical Signal maintains NoSpuriousNotifications == (pending_notifications
   and notified are disjoint) because its NotifyListener action moves a listener
   from `pending_notifications` to `notified` in one ATOMIC step (remove from
   pending AND add to notified together).  This decomposition splits that move
   into a separate MarkNotified (add to `notified`) then RemovePending (remove
   from `pending_notifications`).  Between the two steps the in-flight listener
   is in BOTH sets, so the canonical NoSpuriousNotifications is violated.

   It checks the canonical Signal state (pending_notifications/notified sets)
   against the canonical .cfg invariant `NoSpuriousNotifications`.  TLC finds
   NoSpuriousNotifications violated.

   The entry's interference witness is irreducibility/SignalNotifyDecomposed. *)
EXTENDS Naturals, FiniteSets

CONSTANTS Values, Listeners, NULL

VARIABLES current_value, pending_notifications, notified, inflight, pc

vars == <<current_value, pending_notifications, notified, inflight, pc>>

\* Canonical Signal invariant: a listener is never both pending and notified.
NoSpuriousNotifications ==
    pending_notifications \cap notified = {}

Init ==
    /\ current_value \in Values
    /\ pending_notifications = {}
    /\ notified = {}
    /\ inflight = NULL
    /\ pc = "idle"

\* Begin a notification cycle for a value that differs from the current one.
SetValue(v) ==
    /\ pc = "idle"
    /\ v /= current_value
    /\ current_value' = v
    /\ pending_notifications' = Listeners
    /\ notified' = {}
    /\ UNCHANGED <<inflight, pc>>

\* Step 1: mark a pending listener notified (add to `notified`) WITHOUT removing
\* it from `pending_notifications`.  The canonical NotifyListener does both
\* atomically.
MarkNotified(l) ==
    /\ pc = "idle"
    /\ l \in pending_notifications
    /\ l \notin notified
    /\ notified' = notified \cup {l}
    /\ inflight' = l
    /\ pc' = "removing"
    /\ UNCHANGED <<current_value, pending_notifications>>

\* Step 2: remove the in-flight listener from pending, restoring disjointness.
RemovePending ==
    /\ pc = "removing"
    /\ pending_notifications' = pending_notifications \ {inflight}
    /\ inflight' = NULL
    /\ pc' = "idle"
    /\ UNCHANGED <<current_value, notified>>

Next ==
    \/ \E v \in Values : SetValue(v)
    \/ \E l \in Listeners : MarkNotified(l)
    \/ RemovePending

Spec == Init /\ [][Next]_vars
=============================================================================
