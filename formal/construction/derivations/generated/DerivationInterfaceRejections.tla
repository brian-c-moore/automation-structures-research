---- MODULE DerivationInterfaceRejections ----
EXTENDS BudgetDerivationData, TLC

OmittedActionMap ==
    [action \in Derivation.canonicalActions \ {"CompleteEviction"} |->
        Derivation.actionMap[action]]

MissingActionRecord ==
    [Derivation EXCEPT !.actionMap = OmittedActionMap]

AbsentCommitRecord ==
    [Derivation EXCEPT !.commitActions = {}]

VacuousObligationRecord ==
    [Derivation EXCEPT
        !.witnessObligationStates = Derivation.witnessStates,
        !.witnessViolationStates = {}]

EmptyObservationMap == [field \in {} |-> "unused"]

UnconstrainedObservationRecord ==
    [Derivation EXCEPT
        !.observationFields = {},
        !.observationMap = EmptyObservationMap]

MissingTheoremRecord ==
    [Derivation EXCEPT !.localTheorems = {}]

PrematureRefinementRecord ==
    [Derivation EXCEPT !.refinementStatus = "proved"]

MissingCompleteEvictionWitness ==
    [action \in Derivation.canonicalActions |->
        IF action = "CompleteEviction"
          THEN {}
          ELSE Derivation.witnessActionSteps[action]]

UnboundActionStepRecord ==
    [Derivation EXCEPT
        !.witnessActionSteps = MissingCompleteEvictionWitness]

RejectsMissingAction == ~DerivationRecordAccepted(MissingActionRecord)
RejectsAbsentCommit == ~DerivationRecordAccepted(AbsentCommitRecord)
RejectsVacuousObligation ==
    ~DerivationRecordAccepted(VacuousObligationRecord)
RejectsUnconstrainedObservation ==
    ~DerivationRecordAccepted(UnconstrainedObservationRecord)
RejectsMissingTheorem == ~DerivationRecordAccepted(MissingTheoremRecord)
RejectsPrematureRefinement ==
    ~DerivationRecordAccepted(PrematureRefinementRecord)
RejectsActionStepMismatch ==
    ~DerivationRecordAccepted(UnboundActionStepRecord)

DerivationInit == progressState = "derivation-control"
DerivationNext == UNCHANGED progressState
DerivationSpec == DerivationInit /\ [][DerivationNext]_progressVars

====
