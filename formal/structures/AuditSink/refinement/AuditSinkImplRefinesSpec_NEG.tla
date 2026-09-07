---- MODULE AuditSinkImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated action fault: append the correctly hashed record but leave      *)
(* last_hash stale. Typing, chain links, content binding, genesis, and the   *)
(* concrete hash bound remain checked. HashConsistency is the named seam.   *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS AuditSinkImplRefinesSpec

AdjacentInvariant ==
    TypeInvariant /\ ChainIntegrity /\ HashBindsContent
        /\ LastHashBounded /\ GenesisConsistency

FaultRecord(op) ==
    /\ AdjacentInvariant
    /\ op \in OperationDomain
    /\ Len(log) < max_log_len
    /\ LET new_hash == ContractHash(last_hash, op)
           entry == [operation |-> op, prev_hash |-> last_hash, hash |-> new_hash]
       IN /\ new_hash /= last_hash
          /\ log' = Append(log, entry)
          /\ last_hash' = last_hash
    /\ UNCHANGED max_log_len
    /\ AdjacentInvariant'

FaultNext == (\E op \in OperationDomain : FaultRecord(op)) \/ ImplRead
FaultRefinement == A!Spec
====
