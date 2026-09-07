---- MODULE SignalFromAuditSink ----
\* AuditSink-backed implementation of Signal.
\* The append-only log records actual value changes; each listener owns a pull
\* cursor. A listener is pending when its cursor trails the log head and is
\* notified when its cursor equals a nonempty head. These derived views are
\* disjoint by construction.
\*
\* SetValue invokes AuditSink.Record only when the value changes. NotifyListener
\* advances one cursor to the current head, so no push/notification component is
\* assumed. AuditSink's three chain obligations are checked separately. HashC
\* is the finite TLC realization; the refinement proof is parametric in Hash.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, Listeners, InitialValue, MaxLogLen, Hash(_, _)

ASSUME InitialValue \in Values

\* AuditSink state plus one read cursor per listener.
VARIABLES log, last_hash, cursor

vars == <<log, last_hash, cursor>>

\* Finite TLC realization of Hash. Pos maps the uninterpreted Values elements
\* to distinct enumeration positions; the proof does not unfold this operator.
VN == Cardinality(Values)
VEnum == CHOOSE f \in [1..VN -> Values] :
             \A i, j \in 1..VN : (i /= j) => (f[i] /= f[j])
Pos(v) == CHOOSE i \in 1..VN : VEnum[i] = v
HashC(prev, v) == (prev * 3 + Pos(v) + 1) % 100

\* AuditSink instance. Each recorded operation is the written signal value;
\* MaxLogLen and Hash retain their same-named parameters.
ASink == INSTANCE AuditSink WITH log        <- log,
                                 last_hash  <- last_hash,
                                 Operations <- Values

\* Current value = the value in the most recent change record, or the initial
\* value if no change has been recorded yet.
CurrentValue == IF Len(log) = 0 THEN InitialValue ELSE log[Len(log)].operation

TypeInvariant ==
    /\ ASink!TypeInvariant
    /\ cursor \in [Listeners -> 0..MaxLogLen]
    /\ \A l \in Listeners : cursor[l] <= Len(log)

\* The three AuditSink obligations checked for the component state.
ChainIntegrity   == ASink!ChainIntegrity
HashConsistency  == ASink!HashConsistency
HashBindsContent == ASink!HashBindsContent

Init ==
    /\ ASink!Init
    /\ cursor = [l \in Listeners |-> 0]

\* Record an actual value change. After append, every cursor trails the new head,
\* so the mapped pending set is Listeners and the mapped notified set is empty.
SetValue(v) ==
    /\ v \in Values
    /\ v /= CurrentValue
    /\ ASink!Record(v)
    /\ UNCHANGED cursor

\* Catch listener l up to the log head, moving it from pending to notified.
NotifyListener(l) ==
    /\ l \in Listeners
    /\ cursor[l] < Len(log)
    /\ cursor' = [cursor EXCEPT ![l] = Len(log)]
    /\ UNCHANGED <<log, last_hash>>

Next ==
    \/ \E v \in Values    : SetValue(v)
    \/ \E l \in Listeners : NotifyListener(l)

Spec == Init /\ [][Next]_vars

\* --- Refinement mapping to Signal ---
\* pending  = listeners whose cursor is behind the head (unread change).
\* notified = listeners caught up to a non-empty head (acked latest change).
\* These are disjoint by construction (cursor < Len vs cursor = Len).
MapPending  == { l \in Listeners : cursor[l] < Len(log) }
MapNotified == { l \in Listeners : Len(log) > 0 /\ cursor[l] = Len(log) }

Sig == INSTANCE Signal WITH
        current_value         <- CurrentValue,
        change_observed       <- (Len(log) > 0),
        pending_notifications <- MapPending,
        notified              <- MapNotified,
        Values                <- Values,
        Listeners             <- Listeners

\* Every construction behavior must map to a Signal behavior.
SigRefinement == Sig!Spec

\* The configuration checks this property on the finite instance; the proof
\* module establishes the same refinement parametrically.
====
