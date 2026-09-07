---- MODULE AbsorbThenSqueeze_Proof ----
(***************************************************************************
  TLAPS proof of safety for the AbsorbThenSqueeze composition (sponge pattern).

  Discharges the THEOREM declared in AbsorbThenSqueeze.tla:
      Spec => [](TypeInvariant /\ SqueezeBounded /\ PhaseOrdering)

  Inductive strengthening: the three cfg invariants are jointly inductive
  without further strengthening. The sponge's two-phase structure makes the
  per-action preservation argument straightforward — AbsorbStep increments
  absorb_idx and rotates (rate, capacity) via Permute; FinishAbsorb flips
  the phase flag; SqueezeStep appends to outputs and may rotate state.

  This proof module artifact per the TLA+ study contract
 ***************************************************************************)
EXTENDS AbsorbThenSqueeze, Naturals, Sequences, FiniteSets, TLAPS

ASSUME NumInputsType  == NumInputs  \in Nat /\ NumInputs  >= 1
ASSUME NumOutputsType == NumOutputs \in Nat /\ NumOutputs >= 1

\* Helper: StateValue is a finite set of model values.
LEMMA StateValueElements ==
    /\ v0 \in StateValue
    /\ v1 \in StateValue
    /\ v2 \in StateValue
    /\ v3 \in StateValue
  BY DEF StateValue

\* Helper: InitialRate and InitialCapacity lie in StateValue.
LEMMA InitialRateType == InitialRate \in StateValue
  BY DEF InitialRate, StateValue

LEMMA InitialCapacityType == InitialCapacity \in StateValue
  BY DEF InitialCapacity, StateValue

\* Helper: InputBlock[k] lies in StateValue for k in domain.
LEMMA InputBlockType ==
    \A k \in 1..NumInputs : InputBlock[k] \in StateValue
  BY DEF InputBlock, StateValue

\* Helper: Permute maps any (StateValue, StateValue) pair into
\* StateValue \X StateValue.
LEMMA PermuteType ==
    \A a \in StateValue, b \in StateValue :
        /\ Permute[<<a, b>>] \in StateValue \X StateValue
        /\ Permute[<<a, b>>][1] \in StateValue
        /\ Permute[<<a, b>>][2] \in StateValue
  BY DEF Permute, StateValue

\* Helper: XorWithRate maps any (StateValue, StateValue) pair into StateValue.
LEMMA XorWithRateType ==
    \A a \in StateValue, b \in StateValue :
        XorWithRate[<<a, b>>] \in StateValue
  BY DEF XorWithRate, StateValue

\* Strengthening: the output sequence length tracks the squeeze counter.
\* Init sets both to 0 / 1; SqueezeStep increments both in lockstep; no other
\* action modifies outputs or squeeze_idx. Needed for the SqueezeStep case
\* preservation argument to bound Len(outputs') <= NumOutputs.
OutputsTrackSqueezeIdx == Len(outputs) = squeeze_idx - 1

\* Inductive invariant: the cfg invariants + the strengthening.
Inv == TypeInvariant /\ SqueezeBounded /\ PhaseOrdering /\ OutputsTrackSqueezeIdx

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY InitialRateType, InitialCapacityType, NumInputsType, NumOutputsType
       DEF Init, TypeInvariant
  <1>2. SqueezeBounded
    BY NumOutputsType DEF Init, SqueezeBounded
  <1>3. PhaseOrdering
    BY DEF Init, PhaseOrdering
  <1>4. OutputsTrackSqueezeIdx
    BY DEF Init, OutputsTrackSqueezeIdx
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF Inv

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, SqueezeBounded, PhaseOrdering, OutputsTrackSqueezeIdx
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE AbsorbStep
    \* Extract post-state facts.
    <2>a. phase = "absorb"                                  BY <1>A DEF AbsorbStep
    <2>b. absorb_idx <= NumInputs                            BY <1>A DEF AbsorbStep
    <2>c. rate \in StateValue /\ capacity \in StateValue    OBVIOUS
    <2>d. absorb_idx \in 1..NumInputs                       BY <2>b, NumInputsType
    <2>e. InputBlock[absorb_idx] \in StateValue              BY <2>d, InputBlockType
    <2>f. LET mixed == XorWithRate[<<rate, InputBlock[absorb_idx]>>]
              pair  == Permute[<<mixed, capacity>>]
          IN  /\ mixed \in StateValue
              /\ pair[1] \in StateValue
              /\ pair[2] \in StateValue
      BY <2>c, <2>e, XorWithRateType, PermuteType
    <2>g. rate' = (Permute[<<XorWithRate[<<rate, InputBlock[absorb_idx]>>], capacity>>])[1]
      BY <1>A DEF AbsorbStep
    <2>h. capacity' = (Permute[<<XorWithRate[<<rate, InputBlock[absorb_idx]>>], capacity>>])[2]
      BY <1>A DEF AbsorbStep
    <2>i. absorb_idx' = absorb_idx + 1                       BY <1>A DEF AbsorbStep
    <2>j. UNCHANGED <<phase, squeeze_idx, outputs>>          BY <1>A DEF AbsorbStep
    <2>1. TypeInvariant'
      <3>1. rate' \in StateValue                             BY <2>f, <2>g
      <3>2. capacity' \in StateValue                         BY <2>f, <2>h
      <3>3. phase' = "absorb"                                BY <2>a, <2>j
      <3>4. absorb_idx' \in 1..NumInputs + 1                 BY <2>b, <2>i, NumInputsType
      <3>5. squeeze_idx' \in 1..NumOutputs + 1               BY <2>j
      <3>6. outputs' \in Seq(StateValue)                     BY <2>j
      <3> QED  BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6
    <2>2. SqueezeBounded'
      BY <2>j
    <2>3. PhaseOrdering'
      \* phase' = "absorb"; the antecedent of the implication is false.
      BY <2>a, <2>j
    <2>4. OutputsTrackSqueezeIdx'
      \* outputs and squeeze_idx unchanged.
      BY <2>j
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>B. CASE FinishAbsorb
    <2>a. phase = "absorb"                                  BY <1>B DEF FinishAbsorb
    <2>b. absorb_idx = NumInputs + 1                        BY <1>B DEF FinishAbsorb
    <2>c. phase' = "squeeze"                                 BY <1>B DEF FinishAbsorb
    <2>d. UNCHANGED <<rate, capacity, absorb_idx, squeeze_idx, outputs>>
      BY <1>B DEF FinishAbsorb
    <2>1. TypeInvariant'
      BY <2>c, <2>d, NumInputsType, NumOutputsType
    <2>2. SqueezeBounded'
      BY <2>d
    <2>3. PhaseOrdering'
      BY <2>b, <2>c, <2>d
    <2>4. OutputsTrackSqueezeIdx'
      BY <2>d
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>C. CASE SqueezeStep
    <2>a. phase = "squeeze"                                 BY <1>C DEF SqueezeStep
    <2>b. squeeze_idx <= NumOutputs                          BY <1>C DEF SqueezeStep
    <2>c. outputs' = Append(outputs, rate)                  BY <1>C DEF SqueezeStep
    <2>d. squeeze_idx' = squeeze_idx + 1                     BY <1>C DEF SqueezeStep
    <2>e. UNCHANGED <<phase, absorb_idx>>                    BY <1>C DEF SqueezeStep
    <2>f. rate \in StateValue /\ capacity \in StateValue     OBVIOUS
    <2>g. squeeze_idx \in 1..NumOutputs                     BY <2>b, NumOutputsType
    <2>h. PhaseOrdering                                      OBVIOUS
    <2>i. absorb_idx = NumInputs + 1                        BY <2>a, <2>h
    \* The IF/ELSE on whether to rotate state:
    <2>j. CASE squeeze_idx < NumOutputs
      <3>a. LET pair == Permute[<<rate, capacity>>]
            IN  /\ rate' = pair[1]
                /\ capacity' = pair[2]
        BY <1>C, <2>j DEF SqueezeStep
      <3>b. rate' \in StateValue /\ capacity' \in StateValue
        BY <2>f, <3>a, PermuteType
      <3>1. TypeInvariant'
        <4>1. outputs' \in Seq(StateValue)                   BY <2>c, <2>f
        <4>2. Len(outputs') = Len(outputs) + 1               BY <2>c, <2>f
        <4>3. Len(outputs) <= NumOutputs - 1                  BY <2>b, NumOutputsType
        <4>4. Len(outputs') <= NumOutputs                     BY <4>2, <4>3, NumOutputsType
        <4>5. squeeze_idx' \in 1..NumOutputs + 1              BY <2>b, <2>d, NumOutputsType
        <4>6. absorb_idx' \in 1..NumInputs + 1                BY <2>e, NumInputsType, <2>i
        <4> QED  BY <3>b, <2>a, <2>e, <4>1, <4>4, <4>5, <4>6
      <3>2. SqueezeBounded'
        <4>1. Len(outputs') = Len(outputs) + 1               BY <2>c
        <4>2. Len(outputs) <= NumOutputs - 1                  BY <2>b, NumOutputsType
        <4> QED  BY <4>1, <4>2, NumOutputsType
      <3>3. PhaseOrdering'
        BY <2>a, <2>e, <2>i
      <3>4. OutputsTrackSqueezeIdx'
        <4>1. Len(outputs') = Len(outputs) + 1               BY <2>c, <2>f
        <4>2. squeeze_idx' = squeeze_idx + 1                  BY <2>d
        <4> QED  BY <4>1, <4>2
      <3> QED  BY <3>1, <3>2, <3>3, <3>4
    <2>k. CASE ~(squeeze_idx < NumOutputs)
      <3>a. UNCHANGED <<rate, capacity>>
        BY <1>C, <2>k DEF SqueezeStep
      <3>1. TypeInvariant'
        <4>1. outputs' \in Seq(StateValue)                   BY <2>c, <2>f
        <4>2. Len(outputs') = Len(outputs) + 1               BY <2>c, <2>f
        <4>3. squeeze_idx = NumOutputs                       BY <2>g, <2>k, NumOutputsType
        <4>4. Len(outputs) <= NumOutputs - 1                  BY <2>b, NumOutputsType
        <4>5. Len(outputs') <= NumOutputs                     BY <4>2, <4>4, NumOutputsType
        <4>6. squeeze_idx' \in 1..NumOutputs + 1              BY <4>3, <2>d
        <4>7. absorb_idx' \in 1..NumInputs + 1                BY <2>e, NumInputsType, <2>i
        <4> QED  BY <3>a, <2>a, <2>e, <4>1, <4>5, <4>6, <4>7, <2>f
      <3>2. SqueezeBounded'
        <4>1. Len(outputs') = Len(outputs) + 1               BY <2>c
        <4>2. Len(outputs) <= NumOutputs - 1                  BY <2>b, NumOutputsType
        <4> QED  BY <4>1, <4>2, NumOutputsType
      <3>3. PhaseOrdering'
        BY <2>a, <2>e, <2>i
      <3>4. OutputsTrackSqueezeIdx'
        <4>1. Len(outputs') = Len(outputs) + 1               BY <2>c, <2>f
        <4>2. squeeze_idx' = squeeze_idx + 1                  BY <2>d
        <4> QED  BY <4>1, <4>2
      <3> QED  BY <3>1, <3>2, <3>3, <3>4
    <2> QED  BY <2>j, <2>k
  <1>D. CASE Done
    BY <1>D DEF Done, vars
  <1>E. CASE Next
    BY <1>E, <1>A, <1>B, <1>C, <1>D DEF Next
  <1> QED  BY <1>0, <1>E

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

THEOREM SqueezeBoundedSafety == Spec => []SqueezeBounded
  BY Safety, PTL DEF Inv

THEOREM PhaseOrderingSafety == Spec => []PhaseOrdering
  BY Safety, PTL DEF Inv

====
