---- MODULE QualityHierarchyDerivationRejections ----
EXTENDS QualityHierarchyDerivationData, TLC

VacuousObligationRecord == [Derivation EXCEPT !.obligations = {}]
PrematureRefinementRecord == [Derivation EXCEPT !.refinementStatus = "proved"]

RejectsVacuousObligation == ~DerivationRecordAccepted(VacuousObligationRecord)
RejectsPrematureRefinement == ~DerivationRecordAccepted(PrematureRefinementRecord)

ControlInit == progressState = "QualityHierarchy-rejections"
ControlNext == UNCHANGED progressState
ControlSpec == ControlInit /\ [][ControlNext]_progressVars

====
