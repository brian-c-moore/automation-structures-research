------------------------ MODULE ReductionDecomposed -------------------------
(* Decomposition of reduction.

   Canonical Reduction maintains Partition == (processed and remaining are
   disjoint and cover Items) because its Process action removes an item from
   `remaining` AND adds it to `processed` in one ATOMIC step.  This
   decomposition splits that step into a separate MarkProcessed (add to
   `processed`) then RemoveRemaining (remove from `remaining`).  Between the two
   steps the in-flight item is in BOTH sets, so Partition's disjointness clause
   (processed \cap remaining = {}) is violated.

   It checks the canonical Reduction state (processed/remaining sets) against
   the canonical .cfg invariant `Partition`.  TLC finds Partition violated.

   Differences from the set-based Reduction structure besides the split:
     - `Items` is a literal set here; the structure declares it a CONSTANT
       bound by its configuration.
     - The accumulation is addition.  The structure takes the combine operator
       as CONSTANT Op(_, _) with CONSTANT Identity, both configuration-bound;
       here MarkProcessed computes `result + ItemValue(item)` and Init sets
       `result = 0`.
   Partition below is the structure's, over `processed` and `remaining`;
   `result` appears in no invariant this model checks.

   The entry's Aggregate witness is irreducibility/ReductionAccumulateDecomposed. *)
EXTENDS Naturals, FiniteSets

CONSTANT NULL

Items == {"i1", "i2", "i3"}

VARIABLES result, remaining, processed, current, pc

vars == <<result, remaining, processed, current, pc>>

ItemValue(item) == 1

Init ==
    /\ result = 0
    /\ remaining = Items
    /\ processed = {}
    /\ current = NULL
    /\ pc = "idle"

\* Step 1: mark an item processed (add to `processed`) WITHOUT removing it from
\* `remaining`.  The canonical Process does both in one step.
MarkProcessed(item) ==
    /\ pc = "idle"
    /\ item \in remaining
    /\ item \notin processed
    /\ processed' = processed \cup {item}
    /\ result' = result + ItemValue(item)
    /\ current' = item
    /\ pc' = "removing"
    /\ UNCHANGED remaining

\* Step 2: remove the in-flight item from `remaining`, restoring the partition.
RemoveRemaining ==
    /\ pc = "removing"
    /\ remaining' = remaining \ {current}
    /\ current' = NULL
    /\ pc' = "idle"
    /\ UNCHANGED <<result, processed>>

Next ==
    \/ \E item \in Items : MarkProcessed(item)
    \/ RemoveRemaining

\* Canonical Reduction invariant: processed and remaining partition Items.
Partition ==
    /\ processed \cup remaining = Items
    /\ processed \cap remaining = {}

Spec == Init /\ [][Next]_vars
=============================================================================
