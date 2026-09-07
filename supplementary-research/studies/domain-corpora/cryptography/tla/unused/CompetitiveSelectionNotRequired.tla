---- MODULE CompetitiveSelectionNotRequired ----
(*
  CompetitiveSelection is not required by the cryptographic
  build (the composition taxonomy unused-primitive demonstration).

  Framing (load-bearing — preserve per the study framing §2).
  Not "CompetitiveSelection cannot fit"; "you don't need it to build
  the fifteen algorithms."

  Demonstration. Compose an S-box as `CompetitiveSelection`, where
  byte-input values are "candidates" competing for output-byte "seats."
  The CompetitiveSelection mode (Hard / Soft / Ranked) parameterizes
  how candidates fill seats. For an S-box:
    - There is a single candidate per input value.
    - Each candidate's score is constant (=1; no ranking matters).
    - The allocation function reduces to: input value -> output byte
      via a fixed lookup table.
  Hence CompetitiveSelection degenerates to `ResourceRegistry::lookup
  (input)`. The mode dimension collapses to a constant function. The
  CompetitiveSelection primitive is operationally equivalent to a
  ResourceRegistry lookup; no CompetitiveSelection-specific behavior
  is contributed.

  Modelled instantiation. A 4-entry S-box (`InputDomain = 0..3`,
  `OutputDomain = 0..3`) with a fixed lookup table. The cfg-verified
  invariants demonstrate:
    LookupDeterministic: same input always produces same output
    ScoreIsConstant:     all candidates have score 1
    DegeneratesToLookup: CompetitiveSelection output equals
                         ResourceRegistry lookup output

  `CompetitiveSelectionNotRequired_Proof.tla` proves the stated
  invariants; the finite configuration checks the bounded instance.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets

CONSTANTS
    InputCount

ASSUME InputCountType == InputCount \in Nat /\ InputCount >= 1
ASSUME InputCountConcrete == InputCount = 4

InputDomain == 0..(InputCount - 1)
OutputDomain == 0..(InputCount - 1)
ScoreValue == {0, 1}

\* The S-box: ResourceRegistry-style lookup (input -> output).
SBoxLookup ==
    [k \in InputDomain |->
        IF      k = 0 THEN 3
        ELSE IF k = 1 THEN 2
        ELSE IF k = 2 THEN 1
        ELSE              0]

\* CompetitiveSelection allocation modelled: each candidate (= each
\* input value) has score 1 and gets the seat corresponding to its
\* SBoxLookup output. The "competition" is vacuous.
CSScore(c) == 1
CSAllocation(input) == SBoxLookup[input]

VARIABLES
    input,                  \* current input being processed
    cs_output,              \* CompetitiveSelection output
    rr_output,              \* ResourceRegistry output
    processed               \* TRUE once one input has been processed

vars == <<input, cs_output, rr_output, processed>>

TypeInvariant ==
    /\ input \in InputDomain
    /\ cs_output \in OutputDomain
    /\ rr_output \in OutputDomain
    /\ processed \in BOOLEAN

\* CompetitiveSelection's candidate score is always 1.
ScoreIsConstant ==
    \A k \in InputDomain : CSScore(k) = 1

\* For the same input, CompetitiveSelection and ResourceRegistry
\* produce the same output. CompetitiveSelection degenerates to a
\* ResourceRegistry lookup.
DegeneratesToLookup ==
    processed => cs_output = rr_output

\* Determinism (the S-box's structural property).
LookupDeterministic ==
    \A k1 \in InputDomain, k2 \in InputDomain :
        k1 = k2 => SBoxLookup[k1] = SBoxLookup[k2]

Init ==
    /\ input = 0
    /\ cs_output = 0
    /\ rr_output = 0
    /\ processed = FALSE

Process ==
    /\ ~processed
    /\ cs_output' = CSAllocation(input)
    /\ rr_output' = SBoxLookup[input]
    /\ processed' = TRUE
    /\ UNCHANGED input

ChooseInput ==
    /\ ~processed
    /\ input' \in InputDomain
    /\ UNCHANGED <<cs_output, rr_output, processed>>

Done ==
    /\ processed
    /\ UNCHANGED vars

Next ==
    \/ Process
    \/ ChooseInput
    \/ Done

Spec == Init /\ [][Next]_vars

THEOREM Spec => [](TypeInvariant /\ ScoreIsConstant /\
                   DegeneratesToLookup /\ LookupDeterministic)
====
