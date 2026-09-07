---- MODULE AuditSink_NEG_HashConsistency ----
\* Negative control for HashConsistency. Record appends the new entry but
\* leaves last_hash unchanged. The isolated configuration must reach a
\* HashConsistency violation.

EXTENDS Naturals, Sequences

CONSTANTS Operations, MaxLogLen, Hash(_, _)

VARIABLES log, last_hash

vars == <<log, last_hash>>

HashImpl(prev, op) ==
    (prev * 3 + op + 1) % 100

TypeInvariant ==
    /\ last_hash \in Nat
    /\ Len(log) <= MaxLogLen

ChainIntegrity ==
    \A i \in 2..Len(log) :
        log[i].prev_hash = log[i-1].hash

HashConsistency ==
    IF Len(log) > 0
    THEN last_hash = log[Len(log)].hash
    ELSE last_hash = 0

HashBindsContent ==
    \A i \in 1..Len(log) : log[i].hash = Hash(log[i].prev_hash, log[i].operation)

Init ==
    /\ log = <<>>
    /\ last_hash = 0

Record(op) ==
    /\ Len(log) < MaxLogLen
    /\ LET new_hash == Hash(last_hash, op)
           entry == [operation |-> op, prev_hash |-> last_hash, hash |-> new_hash]
\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
       IN /\ log' = Append(log, entry)
          /\ last_hash' = last_hash
\* ---- MUTATION ENDS.

Next == \E op \in Operations : Record(op)

Spec == Init /\ [][Next]_vars

====
