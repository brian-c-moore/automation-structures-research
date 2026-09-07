---- MODULE CompetitiveSelectionNotRequired_Proof ----
(***************************************************************************
  TLAPS proof of safety for CompetitiveSelectionNotRequired.

  Discharges the THEOREM declared in CompetitiveSelectionNotRequired.tla:
      Spec => [](TypeInvariant /\ ScoreIsConstant /\
                 DegeneratesToLookup /\ LookupDeterministic)

  Inductive strengthening: none. The four cfg invariants are jointly
  inductive. The demonstration's point — CompetitiveSelection
  degenerates to ResourceRegistry::lookup — is closed by
  `DegeneratesToLookup` (cs_output = rr_output once processed).
  `ScoreIsConstant` and `LookupDeterministic` are state-independent
  structural identities that hold by the operator definitions.

  This proof module artifact per the TLA+ study contract.
 ***************************************************************************)
EXTENDS CompetitiveSelectionNotRequired, Naturals, Sequences, FiniteSets, TLAPS

ASSUME InputCountAss      == InputCount \in Nat /\ InputCount >= 1

\* Helper: SBoxLookup returns values in OutputDomain.
LEMMA SBoxLookupType ==
    \A k \in InputDomain : SBoxLookup[k] \in OutputDomain
  BY InputCountConcrete DEF SBoxLookup, InputDomain, OutputDomain

\* Helper: CSAllocation returns values in OutputDomain (since it equals
\* SBoxLookup).
LEMMA CSAllocationType ==
    \A k \in InputDomain : CSAllocation(k) \in OutputDomain
  BY SBoxLookupType DEF CSAllocation

\* 0 is in the domains.
LEMMA ZeroInInputDomain == 0 \in InputDomain
  BY InputCountConcrete DEF InputDomain

LEMMA ZeroInOutputDomain == 0 \in OutputDomain
  BY InputCountConcrete DEF OutputDomain

\* State-independent identities.
LEMMA ScoreIsConstantStatic == ScoreIsConstant
  BY DEF ScoreIsConstant, CSScore, InputDomain

LEMMA LookupDeterministicStatic == LookupDeterministic
  BY DEF LookupDeterministic, InputDomain

Inv == TypeInvariant /\ ScoreIsConstant /\
       DegeneratesToLookup /\ LookupDeterministic

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    <2>a. input = 0 /\ cs_output = 0 /\ rr_output = 0 /\ processed = FALSE
      BY DEF Init
    <2>b. 0 \in InputDomain                               BY ZeroInInputDomain
    <2>c. 0 \in OutputDomain                              BY ZeroInOutputDomain
    <2>d. FALSE \in BOOLEAN                               OBVIOUS
    <2> QED  BY <2>a, <2>b, <2>c, <2>d DEF TypeInvariant
  <1>2. ScoreIsConstant
    BY ScoreIsConstantStatic
  <1>3. DegeneratesToLookup
    \* processed = FALSE at Init; antecedent false.
    BY DEF Init, DegeneratesToLookup
  <1>4. LookupDeterministic
    BY LookupDeterministicStatic
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    <2>1. TypeInvariant'
      BY <1>0 DEF vars
    <2>2. ScoreIsConstant'
      BY ScoreIsConstantStatic DEF ScoreIsConstant
    <2>3. DegeneratesToLookup'
      BY <1>0 DEF vars, DegeneratesToLookup
    <2>4. LookupDeterministic'
      BY LookupDeterministicStatic DEF LookupDeterministic
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>A. CASE Process
    <2>a. ~processed                                      BY <1>A DEF Process
    <2>b. cs_output' = CSAllocation(input)                BY <1>A DEF Process
    <2>c. rr_output' = SBoxLookup[input]                  BY <1>A DEF Process
    <2>d. processed' = TRUE                               BY <1>A DEF Process
    <2>e. UNCHANGED input                                 BY <1>A DEF Process
    <2>f. input \in InputDomain                           OBVIOUS
    <2>g. cs_output' \in OutputDomain                     BY <2>b, <2>f, CSAllocationType
    <2>h. rr_output' \in OutputDomain                     BY <2>c, <2>f, SBoxLookupType
    <2>1. TypeInvariant'
      BY <2>d, <2>e, <2>f, <2>g, <2>h
    <2>2. ScoreIsConstant'
      BY ScoreIsConstantStatic DEF ScoreIsConstant
    <2>3. DegeneratesToLookup'
      \* cs_output' = CSAllocation(input) = SBoxLookup[input] = rr_output'
      <3>1. CSAllocation(input) = SBoxLookup[input]
        BY DEF CSAllocation
      <3> QED  BY <2>b, <2>c, <2>d, <3>1 DEF DegeneratesToLookup
    <2>4. LookupDeterministic'
      BY LookupDeterministicStatic DEF LookupDeterministic
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>B. CASE ChooseInput
    <2>a. ~processed                                      BY <1>B DEF ChooseInput
    <2>b. input' \in InputDomain                          BY <1>B DEF ChooseInput
    <2>c. UNCHANGED <<cs_output, rr_output, processed>>   BY <1>B DEF ChooseInput
    <2>1. TypeInvariant'
      BY <2>b, <2>c
    <2>2. ScoreIsConstant'
      BY ScoreIsConstantStatic DEF ScoreIsConstant
    <2>3. DegeneratesToLookup'
      \* processed' = processed = FALSE; antecedent false.
      BY <2>a, <2>c DEF DegeneratesToLookup
    <2>4. LookupDeterministic'
      BY LookupDeterministicStatic DEF LookupDeterministic
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>C. CASE Done
    <2>1. TypeInvariant'
      BY <1>C DEF Done, vars
    <2>2. ScoreIsConstant'
      BY ScoreIsConstantStatic DEF ScoreIsConstant
    <2>3. DegeneratesToLookup'
      BY <1>C DEF Done, vars, DegeneratesToLookup
    <2>4. LookupDeterministic'
      BY LookupDeterministicStatic DEF LookupDeterministic
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>D. CASE Next
    BY <1>D, <1>A, <1>B, <1>C DEF Next
  <1> QED  BY <1>0, <1>D

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                       BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'        BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeInvariantSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM ScoreIsConstantSafety == Spec => []ScoreIsConstant
  BY Safety, PTL DEF Inv

THEOREM DegeneratesToLookupSafety == Spec => []DegeneratesToLookup
  BY Safety, PTL DEF Inv

THEOREM LookupDeterministicSafety == Spec => []LookupDeterministic
  BY Safety, PTL DEF Inv

====
