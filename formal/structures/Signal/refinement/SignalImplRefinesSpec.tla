---- MODULE SignalImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for Signal. Listener-indexed bool Vecs project  *)
(* to pending and notified sets. num_values and num_listeners are          *)
(* immutable. Same-value writes and membership queries stutter.             *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, FiniteSets

CONSTANTS NumValues, NumListeners
ASSUME ValueCountType == NumValues \in Nat /\ NumValues >= 2
ASSUME ListenerCountType == NumListeners \in Nat /\ NumListeners >= 2
Values == 0..(NumValues - 1)
Listeners == 0..(NumListeners - 1)

VARIABLES num_values, num_listeners,
          current_value, change_observed, pending_notifications, notified
vars == <<num_values, num_listeners,
          current_value, change_observed, pending_notifications, notified>>

S == INSTANCE Signal WITH
        Values <- Values,
        Listeners <- Listeners,
        current_value <- current_value,
        change_observed <- change_observed,
        pending_notifications <- pending_notifications,
        notified <- notified

ImplInvariant ==
    /\ num_values = NumValues
    /\ num_listeners = NumListeners
    /\ S!TypeInvariant
    /\ S!PendingNotifiedDisjointness
    /\ S!NotificationProvenance

Init ==
    /\ num_values = NumValues
    /\ num_listeners = NumListeners
    /\ current_value \in Values
    /\ change_observed = FALSE
    /\ pending_notifications = {}
    /\ notified = {}
    /\ ImplInvariant

ImplSetValue(v) ==
    /\ ImplInvariant
    /\ v \in Values
    /\ v /= current_value
    /\ current_value' = v
    /\ change_observed' = TRUE
    /\ pending_notifications' = Listeners
    /\ notified' = {}
    /\ UNCHANGED <<num_values, num_listeners>>
    /\ ImplInvariant'

ImplNotifyListener(listener) ==
    /\ ImplInvariant
    /\ listener \in pending_notifications
    /\ pending_notifications' = pending_notifications \ {listener}
    /\ notified' = notified \cup {listener}
    /\ UNCHANGED <<num_values, num_listeners,
                    current_value, change_observed>>
    /\ ImplInvariant'

ImplReadOrReject == UNCHANGED vars
ImplNext ==
    \/ \E v \in Values : ImplSetValue(v)
    \/ \E listener \in Listeners : ImplNotifyListener(listener)
    \/ ImplReadOrReject
Spec == Init /\ [][ImplNext]_vars

Refinement == S!Spec
====
