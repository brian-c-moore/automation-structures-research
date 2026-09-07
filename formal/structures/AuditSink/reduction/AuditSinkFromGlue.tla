---- MODULE AuditSinkFromGlue ----
\* Pure-glue re-encoding of AuditSink. `chain` is a CF-006 Buffer and `carry`
\* is a CF-003 Accumulator; no component state is retained.
\*
\* MappedChainIntegrity, MappedHashConsistency, and MappedHashBindsContent are
\* stated over held glue. Refinement is a variable relabeling and does not show
\* that another component supplies the chain obligations. HashCR remains an
\* external cryptographic premise and is not established by this construction.
EXTENDS Naturals, Sequences

CONSTANTS Operations, MaxLogLen, Hash(_, _)

\* Concrete realization for TLC, matching the target's own (AuditSink.tla).
HashImpl(prev, op) ==
    (prev * 3 + op + 1) % 100

\* One Buffer and one Accumulator. No component state.
VARIABLES chain, carry

vars == <<chain, carry>>

TypeInvariant ==
    /\ carry \in Nat
    /\ Len(chain) <= MaxLogLen

\* AuditSink obligations restated over the construction state.
MappedChainIntegrity ==
    \A i \in 2..Len(chain) : chain[i].prev_hash = chain[i-1].hash

MappedHashConsistency ==
    IF Len(chain) > 0 THEN carry = chain[Len(chain)].hash ELSE carry = 0

MappedHashBindsContent ==
    \A i \in 1..Len(chain) :
        chain[i].hash = Hash(chain[i].prev_hash, chain[i].operation)

Init ==
    /\ chain = <<>>
    /\ carry = 0

\* AuditSink Record fuses the hash computation with the append commit; that
\* atomicity is a runtime rely of the construction.
Record(op) ==
    /\ Len(chain) < MaxLogLen
    /\ LET new_hash == Hash(carry, op)
           entry == [operation |-> op, prev_hash |-> carry, hash |-> new_hash]
       IN /\ chain' = Append(chain, entry)
          /\ carry' = new_hash

Next == \E op \in Operations : Record(op)

Spec == Init /\ [][Next]_vars

\* --- Refinement mapping to AuditSink ---
\* Operations, MaxLogLen, and Hash bind implicitly by name; the state
\* variables are relabeled explicitly.
AS == INSTANCE AuditSink WITH
        log       <- chain,
        last_hash <- carry

AuditSinkRefinement == AS!Spec
====
