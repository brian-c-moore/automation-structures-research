------------------ MODULE CompetitiveSelectionSoftDecomposed ------------------
(* A net-zero-transfer instrument. It is not a decomposition of the module it
   names. The original header, retained below, is wrong on four counts:

     - it attributes canonical CompetitiveSelectionSoft a `Redistribute`
       action. There is no such action there; the canonical module's only
       action is `AssignNext`;
     - it holds `weights` as a state VARIABLE, where the canonical module
       DERIVES weights from `extra` (weights[c] = 1 + extra[c]);
     - it fixes its own candidate set as string literals rather than taking
       the CONSTANT;
     - it calls its re-target a move to canonical `Normalization`, "same name,
       same semantics". The name is the same and the predicate is not.
       Canonical Normalization is the guarded implication
       Terminal => WSum[WN] = WeightTotal, so away from the terminal state it
       is vacuously true; this module's is the unconditional
       SumWeights(weights) = WeightTotal. The unconditional form is strictly
       stronger, and it is what makes the mid-transfer shortfall a violation
       here at all.

   The re-target changed the property this instrument checks without
   re-attaching the instrument to the module it names.

   This module is therefore not soft's atomicity evidence. That is
   CompetitiveSelectionSoftMutableScoresDecomposed, a decomposition of
   CompetitiveSelectionSoftMutableScores that computes the score-derived
   quantity and then applies it, run against a model carrying a live-score
   writer, which the canonical module lacks.

   --- The original header, retained as the record of the claim ---

   Decomposition of soft competitive selection.

   Canonical CompetitiveSelectionSoft maintains Normalization == (the weights
   sum to the fixed WeightTotal) because its Redistribute action moves `amount`
   from one candidate to another ATOMICALLY (net-zero: [EXCEPT ![from]=@-amount,
   ![to]=@+amount]).  This decomposition splits that single atomic transfer into
   a separate Withdraw (subtract from `from`) then Deposit (add to `to`).
   Between the two steps the total is short by `amount`, so the canonical
   invariant Normalization is violated.

   The origin spec checked a different property
   (`NormalizationInvariant`, snapshot-consistency of a cached sum).  It is
   re-targeted here to violate the canonical CompetitiveSelectionSoft .cfg
   invariant `Normalization == WSum = WeightTotal` -- same name, same semantics
   (sum of weights = WeightTotal).  TLC finds Normalization violated.          *)
EXTENDS Naturals

CONSTANTS WeightTotal

Candidates == {"c1", "c2", "c3"}

VARIABLES weights, held, pc

vars == <<weights, held, pc>>

\* Sum of all candidate weights (canonical Normalization is WSum[WN]=WeightTotal;
\* over the fixed candidate set this is the same value).
SumWeights(w) == w["c1"] + w["c2"] + w["c3"]

Init ==
    /\ weights \in [Candidates -> 1..WeightTotal]
    /\ SumWeights(weights) = WeightTotal
    /\ held = 0
    /\ pc = "idle"

\* Step 1: withdraw `amount` from `from`.  The canonical Redistribute would also
\* add it to `to` in the SAME step; here it is deferred to Deposit.
Withdraw(from, amount) ==
    /\ pc = "idle"
    /\ amount > 0
    /\ weights[from] - amount > 0       \* canonical universal-contribution guard
    /\ weights' = [weights EXCEPT ![from] = @ - amount]
    /\ held' = amount
    /\ pc' = "transferring"

\* Step 2: deposit the withheld amount into `to`, restoring the total.
Deposit(to) ==
    /\ pc = "transferring"
    /\ weights' = [weights EXCEPT ![to] = @ + held]
    /\ held' = 0
    /\ pc' = "idle"

Next ==
    \/ \E from \in Candidates, amount \in 1..WeightTotal : Withdraw(from, amount)
    \/ \E to \in Candidates : Deposit(to)

\* Canonical CompetitiveSelectionSoft invariant: weights sum to the fixed total.
Normalization ==
    SumWeights(weights) = WeightTotal

Spec == Init /\ [][Next]_vars
=============================================================================
