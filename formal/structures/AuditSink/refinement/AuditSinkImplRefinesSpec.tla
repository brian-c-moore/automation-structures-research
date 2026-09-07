---- MODULE AuditSinkImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for AuditSink. Source:                          *)
(* crate://automation-structures/0.2.3/src/primitives/audit_sink.rs.               *)
(*                                                                         *)
(* max_log_len is immutable and maps to MaxLogLen. log maps the Vec order  *)
(* to a TLA+ sequence of records with operation, prev_hash, and hash fields. *)
(* last_hash maps identically. validate and hash_exec are read-only. The    *)
(* concrete modulo-100 hash carries content binding, not collision          *)
(* resistance; HashCR remains outside this implementation refinement.       *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, Sequences

CONSTANTS MaxOperation, MaxLogLen
ASSUME MaxOperationType == MaxOperation \in Nat
ASSUME MaxLogLenType == MaxLogLen \in Nat

OperationDomain == 0..MaxOperation
ContractHash(prev, op) == (prev * 3 + (op % 100) + 1) % 100

VARIABLES max_log_len, log, last_hash
vars == <<max_log_len, log, last_hash>>

TypeInvariant ==
    /\ max_log_len = MaxLogLen
    /\ last_hash \in Nat
    /\ Len(log) <= max_log_len
ChainIntegrity ==
    \A i \in 2..Len(log) : log[i].prev_hash = log[i-1].hash
HashConsistency ==
    IF Len(log) > 0 THEN last_hash = log[Len(log)].hash ELSE last_hash = 0
HashBindsContent ==
    \A i \in 1..Len(log) :
        log[i].hash = ContractHash(log[i].prev_hash, log[i].operation)
LastHashBounded == last_hash < 100
GenesisConsistency == Len(log) > 0 => log[1].prev_hash = 0
ImplInvariant ==
    TypeInvariant /\ ChainIntegrity /\ HashConsistency /\ HashBindsContent
        /\ LastHashBounded /\ GenesisConsistency

Init ==
    /\ max_log_len = MaxLogLen
    /\ log = <<>>
    /\ last_hash = 0
    /\ ImplInvariant

ImplRecord(op) ==
    /\ ImplInvariant
    /\ op \in OperationDomain
    /\ IF Len(log) < max_log_len
       THEN LET new_hash == ContractHash(last_hash, op)
                entry == [operation |-> op, prev_hash |-> last_hash, hash |-> new_hash]
            IN /\ log' = Append(log, entry)
               /\ last_hash' = new_hash
       ELSE /\ UNCHANGED <<log, last_hash>>
    /\ UNCHANGED max_log_len
    /\ ImplInvariant'

ImplRead == UNCHANGED vars
ImplNext == (\E op \in OperationDomain : ImplRecord(op)) \/ ImplRead
Spec == Init /\ [][ImplNext]_vars

A == INSTANCE AuditSink WITH
        Operations <- OperationDomain,
        MaxLogLen <- MaxLogLen,
        Hash <- ContractHash,
        log <- log,
        last_hash <- last_hash

Refinement == A!Spec
====
