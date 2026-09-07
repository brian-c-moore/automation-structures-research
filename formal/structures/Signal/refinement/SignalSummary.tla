---- MODULE SignalSummary ----
\* Latest-change observation of the same AuditSink summary profile.
\* Listener positions stand for canonical Cursor owners, not delivery flags.
\* No reset, wrap, listener replacement or runtime synchronization is modeled.
EXTENDS AuditSinkSummary

CONSTANTS InitialValue, Listeners
ASSUME InitialValueType == InitialValue \in Operations

VARIABLE cursor
signalVars == <<history, count, carry, latest, cursor>>
CurrentValue == IF Len(latest) = 0 THEN InitialValue ELSE latest[1]
MapPending == {l \in Listeners : cursor[l] < count}
MapNotified == {l \in Listeners : count > 0 /\ cursor[l] = count}

Sig == INSTANCE Signal WITH
    Values <- Operations,
    current_value <- CurrentValue,
    change_observed <- (count > 0),
    pending_notifications <- MapPending,
    notified <- MapNotified

CursorBound == cursor \in [Listeners -> 0..count]
SignalInit == Init /\ cursor = [l \in Listeners |-> 0]

SetValue(value) ==
    /\ value \in Operations
    /\ value /= CurrentValue
    /\ Record(value)
    /\ UNCHANGED cursor

NotifyListener(listener) ==
    /\ listener \in Listeners
    /\ cursor[listener] < count
    /\ cursor' = [cursor EXCEPT ![listener] = count]
    /\ UNCHANGED vars

RefusedSet(value) ==
    /\ value \in Operations
    /\ (value = CurrentValue \/ count >= MaxLogLen)
    /\ UNCHANGED signalVars

RefusedNotify(listener) ==
    /\ listener \in Listeners
    /\ cursor[listener] = count
    /\ UNCHANGED signalVars

SignalNext ==
    \/ \E value \in Operations : SetValue(value) \/ RefusedSet(value)
    \/ \E listener \in Listeners : NotifyListener(listener) \/ RefusedNotify(listener)
SignalSpec == SignalInit /\ [][SignalNext]_signalVars
PendingNotifiedDisjointness == Sig!PendingNotifiedDisjointness
NotificationProvenance == Sig!NotificationProvenance
SignalRefinement == Sig!Spec
====
