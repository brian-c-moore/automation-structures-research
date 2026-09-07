---- MODULE SequentialDerivationRejections ----
EXTENDS SequentialDerivationData, TLC

FalseLivenessRecord ==
    [Derivation EXCEPT
        !.propertyClasses = @ \cup {"liveness"},
        !.transferClasses = @ \cup {"liveness"}]

EmptyCarrierRecord == [Derivation EXCEPT !.executionCarriers = {}]

RejectsFalseLiveness == ~DerivationRecordAccepted(FalseLivenessRecord)
RejectsEmptyCarrier == ~DerivationRecordAccepted(EmptyCarrierRecord)

DerivationInit == progressState = "sequential-rejection"
DerivationNext == UNCHANGED progressState
DerivationSpec == DerivationInit /\ [][DerivationNext]_progressVars

====
