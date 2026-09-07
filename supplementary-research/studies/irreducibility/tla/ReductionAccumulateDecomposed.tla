------------------- MODULE ReductionAccumulateDecomposed --------------------
(* Splits Reduction's Process: CheckItem holds its guard (item in `remaining`);
   Accumulate folds the item into `result` and moves it to `processed`. Two
   workers pass the same item's check and both fold it, so `result` double-
   counts, violating Aggregate. Adds `pc`, `held`, and a second worker.
   (Aggregate constrains `result`, written only by Accumulate; the sibling
   ReductionDecomposed targets Partition instead.) *)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Items, Op(_, _), Identity

VARIABLES result, remaining, processed, pc, held

vars == <<result, remaining, processed, pc, held>>

Procs == {"w1", "w2"}

OpImpl(a, b) == a + b
ItemValue(item) == 1

FoldCount[n \in Nat] ==
    IF n = 0 THEN Identity
    ELSE Op(FoldCount[n - 1], 1)

TypeInvariant ==
    /\ remaining \subseteq Items
    /\ processed \subseteq Items
    /\ result \in Nat

Partition ==
    /\ processed \cup remaining = Items
    /\ processed \cap remaining = {}

Aggregate ==
    result = FoldCount[Cardinality(processed)]

ReassociationBounded ==
    \A n, m \in 0..Cardinality(Items) :
        Op(FoldCount[n], FoldCount[m]) = FoldCount[n + m]

Init ==
    /\ remaining = Items
    /\ processed = {}
    /\ result = Identity
    /\ pc = [p \in Procs |-> "idle"]
    /\ held = [p \in Procs |-> CHOOSE i \in Items : TRUE]

(* Step 1: canonical Process's guard, the item held; no mutation *)
CheckItem(p, item) ==
    /\ pc[p] = "idle"
    /\ item \in remaining
    /\ held' = [held EXCEPT ![p] = item]
    /\ pc' = [pc EXCEPT ![p] = "checked"]
    /\ UNCHANGED <<result, remaining, processed>>

(* Step 2: canonical Process's three writes, on the held item *)
Accumulate(p) ==
    /\ pc[p] = "checked"
    /\ result' = Op(result, ItemValue(held[p]))
    /\ remaining' = remaining \ {held[p]}
    /\ processed' = processed \cup {held[p]}
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED held

Next ==
    \/ \E p \in Procs, i \in Items : CheckItem(p, i)
    \/ \E p \in Procs : Accumulate(p)

Spec == Init /\ [][Next]_vars
=============================================================================
