---- MODULE GovernancePrimitivesNotRequired ----
(*
  Governance primitives (Budget, ...) are not required by the
  cryptographic build (the composition taxonomy unused-primitive demonstration).

  Framing (load-bearing — preserve per the study framing §2).
  Not "Budget cannot fit"; "you don't need Budget to build the fifteen
  algorithms."

  Demonstration. Compose an iterated-transformation using `Budget` to
  bound the round counter. We model Budget as a counter `consumed`
  with a `capacity` upper bound; per round, `consumed' = consumed + 1`.
  The Budget invariant `consumed <= capacity` reduces to
  `consumed <= RoundCount` — the very bound that TraversalEngine
  already enforces (TraversalEngine bounded iteration over
  `0..RoundCount`). No new invariant is contributed; Budget is
  decorative.

  Modelled instantiation. A small iterated-transformation with
  `RoundCount = 4` (TraversalEngine bound) and a parallel Budget
  counter that tracks `consumed`. The cfg-verified invariants:
    BudgetWithinCapacity:  consumed <= capacity
    BudgetEqualsRound:     consumed = round   (Budget is the round counter)
    CapacityIsRoundCount:  capacity = RoundCount  (Budget bound IS the
                                                   TraversalEngine bound)

  `GovernancePrimitivesNotRequired_Proof.tla` proves the stated
  invariants; the finite configuration checks the bounded instance.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets

CONSTANTS
    RoundCount      \* TraversalEngine bound on iteration

ASSUME RoundCountType == RoundCount \in Nat /\ RoundCount >= 1

\* Budget capacity is set to the TraversalEngine bound — the
\* demonstration's central observation.
Capacity == RoundCount

StateValue == 0..3
RoundFn(s) == (s + 1) % 4

VARIABLES
    state,
    round,           \* TraversalEngine counter
    consumed         \* Budget counter

vars == <<state, round, consumed>>

TypeInvariant ==
    /\ state \in StateValue
    /\ round \in 0..RoundCount
    /\ consumed \in 0..Capacity

\* The demonstration's load-bearing invariants.
BudgetWithinCapacity == consumed <= Capacity
BudgetEqualsRound    == consumed = round
CapacityIsRoundCount == Capacity = RoundCount

Init ==
    /\ state = 0
    /\ round = 0
    /\ consumed = 0

Step ==
    /\ round < RoundCount
    /\ consumed < Capacity     \* Budget guard — always coincident with round guard
    /\ state' = RoundFn(state)
    /\ round' = round + 1
    /\ consumed' = consumed + 1

Done ==
    /\ round = RoundCount
    /\ UNCHANGED vars

Next ==
    \/ Step
    \/ Done

Spec == Init /\ [][Next]_vars

THEOREM Spec => [](TypeInvariant /\ BudgetWithinCapacity /\
                   BudgetEqualsRound /\ CapacityIsRoundCount)
====
