---- MODULE Signal_NEG_NotificationProvenance ----
\* Negative control for NotificationProvenance. NotifyListener admits any
\* listener instead of requiring pending membership, so a notification can be
\* recorded before any value change. TypeInvariant
\* and PendingNotifiedDisjointness remain true at the violating state.

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

NotificationProvenance ==
    /\ ~change_observed =>
          pending_notifications = {} /\ notified = {}
    /\ change_observed =>
          pending_notifications \cup notified = Listeners

Init ==
    /\ current_value \in Values
    /\ change_observed = FALSE
    /\ pending_notifications = {}
    /\ notified = {}

SetValue(v) ==
    /\ v /= current_value
    /\ current_value' = v
    /\ change_observed' = TRUE
    /\ pending_notifications' = Listeners
    /\ notified' = {}

NotifyListener(l) ==
    \* Fault: l need not be pending, so this may fire before any change.
    /\ l \in Listeners
    /\ pending_notifications' = pending_notifications \ {l}
    /\ notified' = notified \cup {l}
    /\ UNCHANGED <<current_value, change_observed>>

Next ==
    \/ \E v \in Values : SetValue(v)
    \/ \E l \in Listeners : NotifyListener(l)

Spec == Init /\ [][Next]_vars
====
