---- MODULE FederatedBudget_NEG_MasterCapacityBound ----
\* Negative control for MasterCapacityBound. AllocateSubPool accepts every
\* request instead of enforcing the master ceiling. The isolated configuration
\* must reach a state with master_allocated > MasterCapacity.

EXTENDS Naturals, FiniteSets

CONSTANTS SubPoolNames, MasterCapacity

VARIABLES master_allocated, sub_capacities, sub_allocated

vars == <<master_allocated, sub_capacities, sub_allocated>>

TypeInvariant ==
    /\ master_allocated \in Nat
    /\ sub_capacities \in [SubPoolNames -> Nat]
    /\ sub_allocated \in [SubPoolNames -> Nat]

MasterCapacityBound ==
    master_allocated <= MasterCapacity

SubPoolCapacityBound ==
    \A name \in SubPoolNames : sub_allocated[name] <= sub_capacities[name]

SubN == Cardinality(SubPoolNames)

SubEnum == CHOOSE seq \in [1..SubN -> SubPoolNames] :
               \A n \in SubPoolNames : \E i \in 1..SubN : seq[i] = n

CapSum[i \in 0..SubN] ==
    IF i = 0 THEN 0 ELSE CapSum[i - 1] + sub_capacities[SubEnum[i]]

CapacityConservation ==
    master_allocated = CapSum[SubN]

Init ==
    /\ master_allocated = 0
    /\ sub_capacities = [n \in SubPoolNames |-> 0]
    /\ sub_allocated = [n \in SubPoolNames |-> 0]

\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
AllocateSubPool(name, amount) ==
    IF TRUE
\* ---- MUTATION ENDS.
    THEN /\ master_allocated' = master_allocated + amount
         /\ sub_capacities' = [sub_capacities EXCEPT ![name] = @ + amount]
         /\ UNCHANGED sub_allocated
    ELSE UNCHANGED vars

AllocateFromSubPool(name, amount) ==
    IF sub_allocated[name] + amount <= sub_capacities[name]
    THEN /\ sub_allocated' = [sub_allocated EXCEPT ![name] = @ + amount]
         /\ UNCHANGED <<master_allocated, sub_capacities>>
    ELSE UNCHANGED vars

ReleaseFromSubPool(name, amount) ==
    /\ amount <= sub_allocated[name]
    /\ sub_allocated' = [sub_allocated EXCEPT ![name] = @ - amount]
    /\ UNCHANGED <<master_allocated, sub_capacities>>

Next ==
    \/ \E name \in SubPoolNames, a \in 1..MasterCapacity :
        AllocateSubPool(name, a)
    \/ \E name \in SubPoolNames, a \in 1..MasterCapacity :
        AllocateFromSubPool(name, a)
    \/ \E name \in SubPoolNames, a \in 1..MasterCapacity :
        ReleaseFromSubPool(name, a)

Spec == Init /\ [][Next]_vars

====
