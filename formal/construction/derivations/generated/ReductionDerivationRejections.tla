---- MODULE ReductionDerivationRejections ----
EXTENDS ReductionDerivationData, TLC

VacuousObligationRecord == [Derivation EXCEPT !.obligations = {}]
PrematureRefinementRecord == [Derivation EXCEPT !.refinementStatus = "proved"]

RejectsVacuousObligation == ~DerivationRecordAccepted(VacuousObligationRecord)
RejectsPrematureRefinement == ~DerivationRecordAccepted(PrematureRefinementRecord)

ControlInit == progressState = "Reduction-rejections"
ControlNext == UNCHANGED progressState
ControlSpec == ControlInit /\ [][ControlNext]_progressVars

====
