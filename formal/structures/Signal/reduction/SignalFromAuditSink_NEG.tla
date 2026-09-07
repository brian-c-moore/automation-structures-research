---- MODULE SignalFromAuditSink_NEG ----
\* Negative control for the Signal change filter.
\* SetValue drops v /= CurrentValue, so AuditSink may append a no-op change.
\* That advances the log head and resets the mapped listener views without
\* changing CurrentValue. The step is neither a Signal SetValue, a listener
\* notification, nor a stutter, so SigRefinement must be violated. AuditSink's
\* own chain obligations remain satisfied because Record itself is unchanged.
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, Listeners, InitialValue, MaxLogLen, Hash(_, _)

ASSUME InitialValue \in Values

VARIABLES log, last_hash, cursor
vars == <<log, last_hash, cursor>>

VN == Cardinality(Values)
VEnum == CHOOSE f \in [1..VN -> Values] :
             \A i, j \in 1..VN : (i /= j) => (f[i] /= f[j])
Pos(v) == CHOOSE i \in 1..VN : VEnum[i] = v
HashC(prev, v) == (prev * 3 + Pos(v) + 1) % 100

ASink == INSTANCE AuditSink WITH log        <- log,
                                 last_hash  <- last_hash,
                                 Operations <- Values

CurrentValue == IF Len(log) = 0 THEN InitialValue ELSE log[Len(log)].operation

TypeInvariant ==
    /\ ASink!TypeInvariant
    /\ cursor \in [Listeners -> 0..MaxLogLen]
    /\ \A l \in Listeners : cursor[l] <= Len(log)

ChainIntegrity   == ASink!ChainIntegrity
HashConsistency  == ASink!HashConsistency
HashBindsContent == ASink!HashBindsContent

Init ==
    /\ ASink!Init
    /\ cursor = [l \in Listeners |-> 0]

\* Fault: omit the change-detection guard.
SetValue(v) ==
    /\ v \in Values
    /\ ASink!Record(v)
    /\ UNCHANGED cursor

NotifyListener(l) ==
    /\ l \in Listeners
    /\ cursor[l] < Len(log)
    /\ cursor' = [cursor EXCEPT ![l] = Len(log)]
    /\ UNCHANGED <<log, last_hash>>

Next == (\E v \in Values : SetValue(v)) \/ (\E l \in Listeners : NotifyListener(l))

Spec == Init /\ [][Next]_vars

MapPending  == { l \in Listeners : cursor[l] < Len(log) }
MapNotified == { l \in Listeners : Len(log) > 0 /\ cursor[l] = Len(log) }

Sig == INSTANCE Signal WITH
        current_value <- CurrentValue,
        change_observed <- (Len(log) > 0),
        pending_notifications <- MapPending,
        notified <- MapNotified,
        Values <- Values, Listeners <- Listeners

SigRefinement == Sig!Spec

\* Required outcome: the refinement property is violated while component
\* invariants remain satisfied.
====
