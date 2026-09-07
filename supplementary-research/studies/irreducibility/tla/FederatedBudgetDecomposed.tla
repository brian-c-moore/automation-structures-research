----------------------- MODULE FederatedBudgetDecomposed ----------------------
(* Splits FederatedBudget's AllocateSubPool: CheckSubPool holds its guard
   (`master_allocated + amount <= MasterCapacity`); PerformSubPool applies its
   writes. Two allocators pass the guard with room for one and both perform, so
   master_allocated exceeds MasterCapacity, violating FederationInvariant.
   AllocateFromSubPool and ReleaseFromSubPool stay atomic. Adds `pc`, `pending`,
   and a second allocator. *)
EXTENDS Naturals, FiniteSets

CONSTANTS SubPoolNames, MasterCapacity

VARIABLES master_allocated, sub_capacities, sub_allocated, pc, pending

vars == <<master_allocated, sub_capacities, sub_allocated, pc, pending>>

Procs == {"p1", "p2"}

TypeInvariant ==
    /\ master_allocated \in Nat
    /\ sub_capacities \in [SubPoolNames -> Nat]
    /\ sub_allocated \in [SubPoolNames -> Nat]

FederationInvariant ==
    master_allocated <= MasterCapacity

SubPoolInvariant ==
    \A name \in SubPoolNames : sub_allocated[name] <= sub_capacities[name]

SubN == Cardinality(SubPoolNames)

SubEnum == CHOOSE seq \in [1..SubN -> SubPoolNames] :
               \A n \in SubPoolNames : \E i \in 1..SubN : seq[i] = n

CapSum[i \in 0..SubN] ==
    IF i = 0 THEN 0 ELSE CapSum[i - 1] + sub_capacities[SubEnum[i]]

ConsistencyInvariant ==
    master_allocated = CapSum[SubN]

Init ==
    /\ master_allocated = 0
    /\ sub_capacities = [n \in SubPoolNames |-> 0]
    /\ sub_allocated = [n \in SubPoolNames |-> 0]
    /\ pc = [p \in Procs |-> "idle"]
    /\ pending = [p \in Procs |-> [name |-> SubEnum[1], amount |-> 0]]

(* Step 1: canonical AllocateSubPool's guard, holding the pair it was taken
   for -- no mutation *)
CheckSubPool(p, name, amount) ==
    /\ pc[p] = "idle"
    /\ master_allocated + amount <= MasterCapacity
    /\ pending' = [pending EXCEPT ![p] = [name |-> name, amount |-> amount]]
    /\ pc' = [pc EXCEPT ![p] = "checked"]
    /\ UNCHANGED <<master_allocated, sub_capacities, sub_allocated>>

(* Step 2: canonical AllocateSubPool's mutation, on a guard already passed *)
PerformSubPool(p) ==
    /\ pc[p] = "checked"
    /\ master_allocated' = master_allocated + pending[p].amount
    /\ sub_capacities' = [sub_capacities EXCEPT ![pending[p].name] = @ + pending[p].amount]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<sub_allocated, pending>>

AllocateFromSubPool(name, amount) ==
    IF sub_allocated[name] + amount <= sub_capacities[name]
    THEN /\ sub_allocated' = [sub_allocated EXCEPT ![name] = @ + amount]
         /\ UNCHANGED <<master_allocated, sub_capacities, pc, pending>>
    ELSE UNCHANGED vars

ReleaseFromSubPool(name, amount) ==
    /\ amount <= sub_allocated[name]
    /\ sub_allocated' = [sub_allocated EXCEPT ![name] = @ - amount]
    /\ UNCHANGED <<master_allocated, sub_capacities, pc, pending>>

Next ==
    \/ \E p \in Procs, name \in SubPoolNames, a \in 1..MasterCapacity :
        CheckSubPool(p, name, a)
    \/ \E p \in Procs : PerformSubPool(p)
    \/ \E name \in SubPoolNames, a \in 1..MasterCapacity :
        AllocateFromSubPool(name, a)
    \/ \E name \in SubPoolNames, a \in 1..MasterCapacity :
        ReleaseFromSubPool(name, a)

Spec == Init /\ [][Next]_vars
=============================================================================
