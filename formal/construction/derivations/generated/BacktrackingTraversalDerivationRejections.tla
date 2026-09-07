---- MODULE BacktrackingTraversalDerivationRejections ----
EXTENDS BacktrackingTraversalDerivationData, TLC

VacuousObligationRecord == [Derivation EXCEPT !.obligations = {}]
PrematureRefinementRecord == [Derivation EXCEPT !.refinementStatus = "proved"]

RejectsVacuousObligation == ~DerivationRecordAccepted(VacuousObligationRecord)
RejectsPrematureRefinement == ~DerivationRecordAccepted(PrematureRefinementRecord)

ControlInit == progressState = "BacktrackingTraversal-rejections"
ControlNext == UNCHANGED progressState
ControlSpec == ControlInit /\ [][ControlNext]_progressVars

====
