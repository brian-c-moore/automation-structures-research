---- MODULE Signal ----
EXTENDS Naturals, FiniteSets

CONSTANTS Values, Listeners

VARIABLES current_value, change_observed, pending_notifications, notified

vars == <<current_value, change_observed, pending_notifications, notified>>

TypeInvariant ==
    /\ current_value \in Values
    /\ change_observed \in BOOLEAN
    /\ pending_notifications \subseteq Listeners
    /\ notified \subseteq Listeners

\* Pending and notified are disjoint: no listener is simultaneously awaiting
\* notification and recorded as notified for the current value.
\* SetValue refills pending_notifications and empties notified atomically.
\* NotifyListener removes from pending in the same transition that it adds to
\* notified. The negative control retains the old notified set when refilling
\* pending, making the two views overlap.
PendingNotifiedDisjointness ==
    pending_notifications \cap notified = {}

\* change_observed is armed only by a guarded SetValue transition. Before the first actual
\* value change there is no delivery state. Afterwards every listener is
\* either still pending or recorded as notified for the latest change. With
\* PendingNotifiedDisjointness, this is a partition of Listeners, so a
\* notified listener is tied to a change created only by v /= current.
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
    /\ l \in pending_notifications
    /\ pending_notifications' = pending_notifications \ {l}
    /\ notified' = notified \cup {l}
    /\ UNCHANGED <<current_value, change_observed>>

Next ==
    \/ \E v \in Values : SetValue(v)
    \/ \E l \in Listeners : NotifyListener(l)

Spec == Init /\ [][Next]_vars

\* Signal_Proof proves both delivery-set disjointness and notification
\* provenance for every behavior of Spec.
====
