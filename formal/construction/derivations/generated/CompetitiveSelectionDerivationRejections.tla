---- MODULE CompetitiveSelectionDerivationRejections ----
EXTENDS CompetitiveSelectionDerivationData, TLC

VacuousObligationRecord == [Derivation EXCEPT !.obligations = {}]
PrematureRefinementRecord == [Derivation EXCEPT !.refinementStatus = "proved"]

RejectsVacuousObligation == ~DerivationRecordAccepted(VacuousObligationRecord)
RejectsPrematureRefinement == ~DerivationRecordAccepted(PrematureRefinementRecord)

ControlInit == progressState = "CompetitiveSelection-rejections"
ControlNext == UNCHANGED progressState
ControlSpec == ControlInit /\ [][ControlNext]_progressVars

====
