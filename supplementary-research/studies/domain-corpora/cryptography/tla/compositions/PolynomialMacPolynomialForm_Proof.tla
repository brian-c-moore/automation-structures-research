---- MODULE PolynomialMacPolynomialForm_Proof ----
(***************************************************************************
  TLAPS proof of safety for PolynomialMacPolynomialForm.
  Sibling of PolynomialMacHornerForm_Proof.

  Discharges the THEOREM declared in PolynomialMacPolynomialForm.tla:
      Spec => [](TypeInvariant /\ PartialSumCorrect)

  Inductive strengthening: none. Both invariants jointly inductive.

  This proof module per the written two-form decomposition.
 ***************************************************************************)
EXTENDS PolynomialMacPolynomialForm, Naturals, Sequences, FiniteSets, TLAPS

ASSUME PAss      == P \in Nat /\ P >= 5
ASSUME RAss      == R \in Nat /\ R < P
ASSUME BlocksAss == Blocks \in Nat /\ Blocks >= 1 /\ Blocks <= 4

\* Helper: FieldZero, R, and InputBlock are in Field.
LEMMA FieldZeroType == FieldZero \in Field
  BY PAss DEF FieldZero, Field

LEMMA RFieldType == R \in Field
  BY RAss, PAss DEF Field

LEMMA InputBlockType ==
    \A k \in 1..Blocks : InputBlock[k] \in Field
  BY PAss, BlocksAss DEF InputBlock, Field

LEMMA AddType ==
    \A a, b \in Field : Add(a, b) \in Field
  BY PAss DEF Add, Field

LEMMA MulType ==
    \A a, b \in Field : Mul(a, b) \in Field
  BY PAss DEF Mul, Field

\* Helper: PowerAt(k) is in Field for k in 1..Blocks.
LEMMA PowerAtType ==
    \A k \in 1..Blocks : PowerAt(k) \in Field
  BY RFieldType, MulType, BlocksAss DEF PowerAt

\* Helper: LaneProduct(i) is in Field for i in 1..Blocks.
LEMMA LaneProductType ==
    \A i \in 1..Blocks : LaneProduct(i) \in Field
  <1> SUFFICES ASSUME NEW i \in 1..Blocks PROVE LaneProduct(i) \in Field
    OBVIOUS
  <1>1. InputBlock[i] \in Field                            BY InputBlockType
  <1>2. Blocks - i + 1 \in 1..Blocks                       BY BlocksAss
  <1>3. PowerAt(Blocks - i + 1) \in Field                  BY <1>2, PowerAtType
  <1> QED  BY <1>1, <1>3, MulType DEF LaneProduct

\* Helper: ExpectedSumAt(k) is in Field for k in 0..Blocks.
LEMMA ExpectedSumAtType ==
    \A k \in 0..Blocks : ExpectedSumAt(k) \in Field
  <1> SUFFICES ASSUME NEW k \in 0..Blocks PROVE ExpectedSumAt(k) \in Field
    OBVIOUS
  <1>1. FieldZero \in Field                                BY FieldZeroType
  <1>2. \A i \in 1..Blocks : LaneProduct(i) \in Field      BY LaneProductType
  <1>3. CASE k = 0
    BY <1>1, <1>3 DEF ExpectedSumAt
  <1>4. CASE k = 1
    BY <1>1, <1>2, AddType, BlocksAss, <1>4 DEF ExpectedSumAt
  <1>5. CASE k = 2
    BY <1>1, <1>2, AddType, BlocksAss, <1>5 DEF ExpectedSumAt
  <1>6. CASE k = 3
    BY <1>1, <1>2, AddType, BlocksAss, <1>6 DEF ExpectedSumAt
  <1>7. CASE k = 4
    BY <1>1, <1>2, AddType, BlocksAss, <1>7 DEF ExpectedSumAt
  <1> QED  BY BlocksAss, <1>3, <1>4, <1>5, <1>6, <1>7

\* Helper: ExpectedSumAt is incrementally correct: ExpectedSumAt(k+1) =
\* Add(ExpectedSumAt(k), LaneProduct(k+1)).
LEMMA ExpectedSumStep ==
    \A k \in 0..(Blocks - 1) :
        ExpectedSumAt(k + 1) = Add(ExpectedSumAt(k), LaneProduct(k + 1))
  <1> SUFFICES ASSUME NEW k \in 0..(Blocks - 1)
               PROVE  ExpectedSumAt(k + 1) = Add(ExpectedSumAt(k), LaneProduct(k + 1))
    OBVIOUS
  <1>1. CASE k = 0
    BY <1>1 DEF ExpectedSumAt
  <1>2. CASE k = 1
    BY <1>2 DEF ExpectedSumAt
  <1>3. CASE k = 2
    BY <1>3 DEF ExpectedSumAt
  <1>4. CASE k = 3
    BY <1>4 DEF ExpectedSumAt
  <1> QED  BY BlocksAss, <1>1, <1>2, <1>3, <1>4

\* Inductive invariant.
Inv == TypeInvariant /\ PartialSumCorrect

(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY FieldZeroType, BlocksAss DEF Init, TypeInvariant
  <1>2. PartialSumCorrect
    BY FieldZeroType DEF Init, PartialSumCorrect, ExpectedSumAt
  <1> QED  BY <1>1, <1>2 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, PartialSumCorrect
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE ComputeAndAddLane
    <2>a. lane_idx < Blocks                                BY <1>A DEF ComputeAndAddLane
    <2>b. running_sum' = Add(running_sum, LaneProduct(lane_idx + 1))
      BY <1>A DEF ComputeAndAddLane
    <2>c. lane_idx' = lane_idx + 1                         BY <1>A DEF ComputeAndAddLane
    <2>d. running_sum \in Field                            OBVIOUS
    <2>e. lane_idx + 1 \in 1..Blocks                       BY <2>a, BlocksAss
    <2>f. LaneProduct(lane_idx + 1) \in Field              BY <2>e, LaneProductType
    <2>g. running_sum' \in Field                           BY <2>b, <2>d, <2>f, AddType
    <2>1. TypeInvariant'
      BY <2>a, <2>c, <2>g, BlocksAss
    <2>2. PartialSumCorrect'
      <3>1. running_sum = ExpectedSumAt(lane_idx)           OBVIOUS
      <3>2. lane_idx \in 0..(Blocks - 1)                    BY <2>a, BlocksAss
      <3>3. ExpectedSumAt(lane_idx + 1) =
              Add(ExpectedSumAt(lane_idx), LaneProduct(lane_idx + 1))
        BY <3>2, ExpectedSumStep
      <3>4. running_sum' = ExpectedSumAt(lane_idx + 1)
        BY <2>b, <3>1, <3>3
      <3> QED  BY <2>c, <3>4
    <2> QED  BY <2>1, <2>2
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

THEOREM PartialSumCorrectSafety == Spec => []PartialSumCorrect
  BY Safety, PTL DEF Inv

====
