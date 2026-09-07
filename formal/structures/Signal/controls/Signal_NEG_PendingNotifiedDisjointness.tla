---- MODULE Signal_NEG_PendingNotifiedDisjointness ----
\* Negative control for PendingNotifiedDisjointness.
\* SetValue refills pending but retains listeners already in notified. The
\* isolated configuration must report an overlap after a later value change.

EXTENDS Naturals, FiniteSets

CONSTANTS Values, Listeners

VARIABLES current_value, change_observed, pending_notifications, notified

vars == <<current_value, change_observed, pending_notifications, notified>>

TypeInvariant ==
    /\ current_value \in Values
    /\ change_observed \in BOOLEAN
    /\ pending_notifications \subseteq Listeners
    /\ notified \subseteq Listeners

PendingNotifiedDisjointness ==
    pending_notifications \cap notified = {}

Init ==
    /\ current_value \in Values
    /\ change_observed = FALSE
    /\ pending_notifications = {}
    /\ notified = {}

SetValue(v) ==
    /\ v /= current_value
    /\ current_value' = v
    /\ change_observed' = TRUE
\* Fault: retain notified while refilling pending.
    /\ pending_notifications' = Listeners
    /\ UNCHANGED notified

NotifyListener(l) ==
    /\ l \in pending_notifications
    /\ pending_notifications' = pending_notifications \ {l}
    /\ notified' = notified \cup {l}
    /\ UNCHANGED <<current_value, change_observed>>

Next ==
    \/ \E v \in Values : SetValue(v)
    \/ \E l \in Listeners : NotifyListener(l)

Spec == Init /\ [][Next]_vars

====
