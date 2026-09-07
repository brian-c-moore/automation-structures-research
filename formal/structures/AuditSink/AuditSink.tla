---- MODULE AuditSink ----
EXTENDS Naturals, Sequences

CONSTANTS Operations, MaxLogLen, Hash(_, _)

VARIABLES log, last_hash

vars == <<log, last_hash>>

\* The chain hash depends on both the previous hash and the operation, so each
\* record binds its content as well as its position. TLC realizes Hash with
\* HashImpl. Tamper evidence additionally relies on the external HashCR
\* premise stated by AuditSink_Proof.
HashImpl(prev, op) ==
    (prev * 3 + op + 1) % 100

\* Record is the only action; the model has no adversarial tamper transition.
\* The append and last_hash update are one atomic commit.

\* Record admits an append only below MaxLogLen, and the configured Hash
\* realization returns a natural. These are carrier representation bounds,
\* not cryptographic guarantees.
TypeInvariant ==
    /\ last_hash \in Nat
    /\ Len(log) <= MaxLogLen

\* Hash chain integrity: each record's prev_hash matches the previous record's hash
ChainIntegrity ==
    \A i \in 2..Len(log) :
        log[i].prev_hash = log[i-1].hash

\* Consistency: last_hash always equals the most recent record's hash
HashConsistency ==
    IF Len(log) > 0
    THEN last_hash = log[Len(log)].hash
    ELSE last_hash = 0

\* Content binding: each record's hash covers its previous hash AND its operation.
\* Combined with a collision-resistant Hash, altering any record's content or
\* prev_hash changes the hash it must carry, making tampering detectable.
HashBindsContent ==
    \A i \in 1..Len(log) : log[i].hash = Hash(log[i].prev_hash, log[i].operation)

Init ==
    /\ log = <<>>
    /\ last_hash = 0

Record(op) ==
    /\ Len(log) < MaxLogLen
    /\ LET new_hash == Hash(last_hash, op)
           entry == [operation |-> op, prev_hash |-> last_hash, hash |-> new_hash]
       IN /\ log' = Append(log, entry)
          /\ last_hash' = new_hash

Next == \E op \in Operations : Record(op)

Spec == Init /\ [][Next]_vars

\* AuditSink_Proof proves the three public invariants under the stated Hash
\* and bound assumptions.
====
