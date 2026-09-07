----------------- MODULE AllocationSnapshotAcceptDecomposed -----------------
(* Splits AllocationSnapshot's AcceptNode: CheckAccept holds its guards (node
   unaccepted, cost fits budget); PerformAccept accepts and deducts. Two
   accepters pass the budget check with room for one and both deduct, so
   budget_remaining goes below zero, violating TypeInvariant's
   `budget_remaining \in Nat` (the .cfg lists it first; BudgetConsistency is a
   sum invariant and holds). Adds `pc`, `held`, and a second accepter. *)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, BudgetCapacity

VARIABLES accepted, total_cost, budget_remaining, pc, held

vars == <<accepted, total_cost, budget_remaining, pc, held>>

Procs == {"p1", "p2"}

TypeInvariant ==
    /\ accepted \subseteq Nodes
    /\ total_cost \in Nat
    /\ budget_remaining \in Nat

BudgetConsistency ==
    total_cost + budget_remaining <= BudgetCapacity

Init ==
    /\ accepted = {}
    /\ total_cost = 0
    /\ budget_remaining = BudgetCapacity
    /\ pc = [p \in Procs |-> "idle"]
    /\ held = [p \in Procs |-> [node |-> CHOOSE n \in Nodes : TRUE, cost |-> 0]]

(* Step 1: canonical AcceptNode's two guards, the pair held; no mutation *)
CheckAccept(p, n, node_cost) ==
    /\ pc[p] = "idle"
    /\ n \notin accepted
    /\ node_cost <= budget_remaining
    /\ held' = [held EXCEPT ![p] = [node |-> n, cost |-> node_cost]]
    /\ pc' = [pc EXCEPT ![p] = "checked"]
    /\ UNCHANGED <<accepted, total_cost, budget_remaining>>

(* Step 2: canonical AcceptNode's three writes, on guards already passed *)
PerformAccept(p) ==
    /\ pc[p] = "checked"
    /\ accepted' = accepted \cup {held[p].node}
    /\ total_cost' = total_cost + held[p].cost
    /\ budget_remaining' = budget_remaining - held[p].cost
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED held

Next ==
    \/ \E p \in Procs, n \in Nodes, c \in 1..BudgetCapacity : CheckAccept(p, n, c)
    \/ \E p \in Procs : PerformAccept(p)

Spec == Init /\ [][Next]_vars
=============================================================================
