---- MODULE GovernancePrimitivesNotRequired_Proof ----
(***************************************************************************
  TLAPS proof of safety for GovernancePrimitivesNotRequired.

  Discharges the THEOREM declared in GovernancePrimitivesNotRequired.tla:
      Spec => [](TypeInvariant /\ BudgetWithinCapacity /\
                 BudgetEqualsRound /\ CapacityIsRoundCount)

  Inductive strengthening: none. The four cfg invariants are jointly
  inductive. The demonstration's point — Budget's consumed-counter
  invariant `consumed <= capacity` reduces to TraversalEngine's
  bound — is closed by `BudgetEqualsRound` (consumed = round) plus
  `CapacityIsRoundCount` (capacity = RoundCount); the cfg-checked
  conjunction proves Budget is decorative.

  This proof module artifact per the TLA+ study contract.
 ***************************************************************************)
EXTENDS GovernancePrimitivesNotRequired, Naturals, Sequences, FiniteSets, TLAPS

ASSUME RoundCountAss      == RoundCount \in Nat /\ RoundCount >= 1

\* Helper: RoundFn closure.
LEMMA RoundFnType ==
    \A s \in StateValue : RoundFn(s) \in StateValue
  BY DEF RoundFn, StateValue

LEMMA ZeroInStateValue == 0 \in StateValue
  BY DEF StateValue

Inv == TypeInvariant /\ BudgetWithinCapacity /\
       BudgetEqualsRound /\ CapacityIsRoundCount

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    <2>a. state = 0 /\ round = 0 /\ consumed = 0           BY DEF Init
    <2>b. 0 \in StateValue                                  BY ZeroInStateValue
    <2>c. 0 \in 0..RoundCount                               BY RoundCountAss
    <2>d. 0 \in 0..Capacity                                 BY RoundCountAss DEF Capacity
    <2> QED  BY <2>a, <2>b, <2>c, <2>d DEF TypeInvariant
  <1>2. BudgetWithinCapacity
    BY RoundCountAss DEF Init, BudgetWithinCapacity, Capacity
  <1>3. BudgetEqualsRound
    BY DEF Init, BudgetEqualsRound
  <1>4. CapacityIsRoundCount
    BY DEF Capacity, CapacityIsRoundCount
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, BudgetWithinCapacity,
              BudgetEqualsRound, CapacityIsRoundCount
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE Step
    <2>a. round < RoundCount                              BY <1>A DEF Step
    <2>b. consumed < Capacity                             BY <1>A DEF Step
    <2>c. state' = RoundFn(state)                         BY <1>A DEF Step
    <2>d. round' = round + 1                              BY <1>A DEF Step
    <2>e. consumed' = consumed + 1                        BY <1>A DEF Step
    <2>f. state \in StateValue                            OBVIOUS
    <2>g. state' \in StateValue                           BY <2>c, <2>f, RoundFnType
    <2>h. round \in 0..RoundCount                         OBVIOUS
    <2>i. consumed \in 0..Capacity                        OBVIOUS
    <2>j. round' \in 0..RoundCount
      BY <2>a, <2>d, <2>h, RoundCountAss
    <2>k. consumed' \in 0..Capacity
      BY <2>b, <2>e, <2>i, RoundCountAss DEF Capacity
    <2>1. TypeInvariant'
      BY <2>g, <2>j, <2>k
    <2>2. BudgetWithinCapacity'
      BY <2>b, <2>e, RoundCountAss DEF Capacity
    <2>3. BudgetEqualsRound'
      \* consumed' = consumed + 1 = round + 1 = round'
      <3>1. consumed = round                              OBVIOUS
      <3> QED  BY <3>1, <2>d, <2>e
    <2>4. CapacityIsRoundCount'
      BY DEF Capacity
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>B. CASE Done
    BY <1>B DEF Done, vars
  <1>C. CASE Next
    BY <1>C, <1>A, <1>B DEF Next
  <1> QED  BY <1>0, <1>C

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                       BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'        BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeInvariantSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM BudgetWithinCapacitySafety == Spec => []BudgetWithinCapacity
  BY Safety, PTL DEF Inv

THEOREM BudgetEqualsRoundSafety == Spec => []BudgetEqualsRound
  BY Safety, PTL DEF Inv

THEOREM CapacityIsRoundCountSafety == Spec => []CapacityIsRoundCount
  BY Safety, PTL DEF Inv

====
