--------------------- MODULE SignalNotifyDecomposed ------------------------
(* Splits Signal's NotifyListener into RemovePending (drop from
   `pending_notifications`) then AddNotified (add to `notified`). Canonical's
   own SetValue fires between and refills `pending_notifications`, so AddNotified
   leaves the listener in both sets, violating NoSpuriousNotifications. Adds
   `pc` and `held`. (The drop is ordered first so a lone actor stays disjoint;
   the sibling SignalDecomposed orders the other way and shows the transient.) *)
EXTENDS Naturals, FiniteSets

CONSTANTS Values, Listeners

VARIABLES current_value, pending_notifications, notified, pc, held

vars == <<current_value, pending_notifications, notified, pc, held>>

TypeInvariant ==
    /\ current_value \in Values
    /\ pending_notifications \subseteq Listeners
    /\ notified \subseteq Listeners

NoSpuriousNotifications ==
    pending_notifications \cap notified = {}

Init ==
    /\ current_value \in Values
    /\ pending_notifications = {}
    /\ notified = {}
    /\ pc = "idle"
    /\ held = CHOOSE l \in Listeners : TRUE

SetValue(v) ==
    /\ v /= current_value
    /\ current_value' = v
    /\ pending_notifications' = Listeners
    /\ notified' = {}
    /\ UNCHANGED <<pc, held>>

(* Step 1: canonical NotifyListener's drop from pending, the listener held; the
   add to notified is deferred *)
RemovePending(l) ==
    /\ pc = "idle"
    /\ l \in pending_notifications
    /\ pending_notifications' = pending_notifications \ {l}
    /\ held' = l
    /\ pc' = "notifying"
    /\ UNCHANGED <<current_value, notified>>

(* Step 2: canonical NotifyListener's add to notified, on the held listener *)
AddNotified ==
    /\ pc = "notifying"
    /\ notified' = notified \cup {held}
    /\ pc' = "idle"
    /\ UNCHANGED <<current_value, pending_notifications, held>>

Next ==
    \/ \E v \in Values : SetValue(v)
    \/ \E l \in Listeners : RemovePending(l)
    \/ AddNotified

Spec == Init /\ [][Next]_vars
=============================================================================
