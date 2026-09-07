---- MODULE AllocationSnapshotImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for AllocationSnapshot. The accepted Vec is     *)
(* observed as a set because distinctness makes order unobservable to the  *)
(* canonical machine. capacity and num_nodes are immutable; u64 values map *)
(* to Nat. capture is a finite sequence of ImplAccept or stutter steps.     *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, FiniteSets

CONSTANTS Capacity, NumNodes
ASSUME CapacityType == Capacity \in Nat /\ Capacity >= 1
ASSUME NumNodesType == NumNodes \in Nat /\ NumNodes >= 1

NodeSet == 0..(NumNodes - 1)

VARIABLES capacity, num_nodes, accepted, total_cost, budget_remaining
vars == <<capacity, num_nodes, accepted, total_cost, budget_remaining>>

TypeInvariant ==
    /\ capacity = Capacity
    /\ num_nodes = NumNodes
    /\ accepted \subseteq NodeSet
    /\ total_cost \in Nat
    /\ budget_remaining \in Nat
BudgetConsistency == total_cost + budget_remaining <= capacity
ImplInvariant == TypeInvariant /\ BudgetConsistency

Init ==
    /\ capacity = Capacity
    /\ num_nodes = NumNodes
    /\ accepted = {}
    /\ total_cost = 0
    /\ budget_remaining = capacity
    /\ ImplInvariant

ImplAccept(n, cost) ==
    /\ ImplInvariant
    /\ n \in NodeSet
    /\ n \notin accepted
    /\ cost \in 1..budget_remaining
    /\ accepted' = accepted \cup {n}
    /\ total_cost' = total_cost + cost
    /\ budget_remaining' = budget_remaining - cost
    /\ UNCHANGED <<capacity, num_nodes>>
    /\ ImplInvariant'

ImplReadOrReject == UNCHANGED vars
ImplNext ==
    (\E n \in NodeSet, cost \in 1..Capacity : ImplAccept(n, cost))
        \/ ImplReadOrReject
Spec == Init /\ [][ImplNext]_vars

A == INSTANCE AllocationSnapshot WITH
        Nodes <- NodeSet,
        BudgetCapacity <- Capacity,
        accepted <- accepted,
        total_cost <- total_cost,
        budget_remaining <- budget_remaining

Refinement == A!Spec
====
