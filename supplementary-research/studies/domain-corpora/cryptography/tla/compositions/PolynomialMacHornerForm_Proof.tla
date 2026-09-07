---- MODULE PolynomialMacHornerForm_Proof ----
(***************************************************************************
  TLAPS proof of safety for the PolynomialMacHornerForm composition, the
  Horner half of the written two-form decomposition.

  Discharges the THEOREM declared in PolynomialMacHornerForm.tla:
      Spec => [](TypeInvariant /\ HistoryStartsAtZero
                 /\ HornerChainConsistent /\ ChainedAccCorrect)

  Inductive strengthening: none. Four cfg invariants jointly inductive.

  This proof module covers the Horner-form component of the written
  two-form polynomial-MAC decomposition.
 ***************************************************************************)
EXTENDS PolynomialMacHornerForm, Naturals, Sequences, FiniteSets, TLAPS

ASSUME PAss      == P \in Nat /\ P >= 5
ASSUME RAss      == R \in Nat /\ R < P
ASSUME BlocksAss == Blocks \in Nat /\ Blocks >= 1

\* Helper: FieldZero is in Field.
LEMMA FieldZeroType == FieldZero \in Field
  BY PAss DEF FieldZero, Field

\* Helper: InputBlock[k] is in Field.
LEMMA InputBlockType ==
    \A k \in 1..Blocks : InputBlock[k] \in Field
  BY PAss, BlocksAss DEF InputBlock, Field

\* Helper: Add and Mul return Field elements.
LEMMA AddType ==
    \A a, b \in Field : Add(a, b) \in Field
  BY PAss DEF Add, Field

LEMMA MulType ==
    \A a, b \in Field : Mul(a, b) \in Field
  BY PAss DEF Mul, Field

\* Helper: R is in Field.
LEMMA RFieldType == R \in Field
  BY RAss, PAss DEF Field

\* Inductive invariant.
Inv == TypeInvariant /\ HistoryStartsAtZero
       /\ HornerChainConsistent /\ ChainedAccCorrect

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY FieldZeroType, BlocksAss DEF Init, TypeInvariant
  <1>2. HistoryStartsAtZero
    BY DEF Init, HistoryStartsAtZero
  <1>3. HornerChainConsistent
    BY DEF Init, HornerChainConsistent
  <1>4. ChainedAccCorrect
    BY DEF Init, ChainedAccCorrect
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF Inv

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, HistoryStartsAtZero,
              HornerChainConsistent, ChainedAccCorrect
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE HornerStep
    <2>a. idx < Blocks                                     BY <1>A DEF HornerStep
    <2> DEFINE next == Mul(Add(accumulator, InputBlock[idx + 1]), R)
    <2>b. accumulator' = next                              BY <1>A DEF HornerStep
    <2>c. history' = Append(history, next)                 BY <1>A DEF HornerStep
    <2>d. idx' = idx + 1                                   BY <1>A DEF HornerStep
    <2>e. accumulator \in Field                            OBVIOUS
    <2>f. idx + 1 \in 1..Blocks                            BY <2>a, BlocksAss
    <2>g. InputBlock[idx + 1] \in Field                    BY <2>f, InputBlockType
    <2>h. Add(accumulator, InputBlock[idx + 1]) \in Field  BY <2>e, <2>g, AddType
    <2>i. next \in Field                                   BY <2>h, RFieldType, MulType
    <2>j. Len(history) = idx + 1                           OBVIOUS
    <2>k. history \in Seq(Field)                           OBVIOUS
    <2>l. history' \in Seq(Field) /\ Len(history') = idx + 2
      BY <2>c, <2>i, <2>j, <2>k
    <2>1. TypeInvariant'
      BY <2>a, <2>b, <2>d, <2>i, <2>l, BlocksAss
    <2>2. HistoryStartsAtZero'
      <3>1. history[1] = FieldZero                          OBVIOUS
      <3>2. Len(history) >= 1                               BY <2>j, BlocksAss
      <3>3. history'[1] = history[1]
        BY <2>c, <2>j, <3>2
      <3> QED  BY <3>1, <3>3
    <2>3. HornerChainConsistent'
      <3> SUFFICES ASSUME NEW k \in 1..idx'
                   PROVE  history'[k + 1] = Mul(Add(history'[k], InputBlock[k]), R)
        OBVIOUS
      <3>A. CASE k \in 1..idx
        <4>1. k + 1 \in 1..Len(history)                     BY <2>j, <3>A
        <4>2. k \in 1..Len(history)                         BY <2>j, <3>A
        <4>3. history'[k + 1] = history[k + 1]
          BY <2>c, <2>j, <4>1
        <4>4. history'[k] = history[k]
          BY <2>c, <2>j, <4>2
        <4>5. history[k + 1] = Mul(Add(history[k], InputBlock[k]), R)
          BY <3>A
        <4> QED  BY <4>3, <4>4, <4>5
      <3>B. CASE k = idx + 1
        <4>1. history'[k + 1] = next
          BY <2>c, <2>j, <3>B
        <4>2. history'[k] = history[idx + 1]
          BY <2>c, <2>j, <3>B
        <4>3. history[idx + 1] = accumulator
          \* From ChainedAccCorrect pre.
          BY <2>j
        <4>4. next = Mul(Add(accumulator, InputBlock[idx + 1]), R)
          OBVIOUS
        <4>5. k = idx + 1                                   BY <3>B
        <4> QED  BY <4>1, <4>2, <4>3, <4>4, <4>5
      <3> QED  BY <2>d, <3>A, <3>B
    <2>4. ChainedAccCorrect'
      <3>1. history'[Len(history')] = next
        BY <2>c, <2>i, <2>j, <2>k
      <3> QED  BY <2>b, <3>1
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>B. CASE Done
    BY <1>B DEF Done, vars
  <1>C. CASE Next
    BY <1>C, <1>A, <1>B DEF Next
  <1> QED  BY <1>0, <1>C

(*-------------------------------------------------------------------------*)
(* Main safety theorem.                                                    *)
(*-------------------------------------------------------------------------*)
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                       BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'        BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

(*-------------------------------------------------------------------------*)
(* Per-invariant corollaries.                                              *)
(*-------------------------------------------------------------------------*)
THEOREM TypeInvariantSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM HistoryStartsAtZeroSafety == Spec => []HistoryStartsAtZero
  BY Safety, PTL DEF Inv

THEOREM HornerChainConsistentSafety == Spec => []HornerChainConsistent
  BY Safety, PTL DEF Inv

THEOREM ChainedAccCorrectSafety == Spec => []ChainedAccCorrect
  BY Safety, PTL DEF Inv

====
