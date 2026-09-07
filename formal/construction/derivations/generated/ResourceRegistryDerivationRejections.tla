---- MODULE ResourceRegistryDerivationRejections ----
EXTENDS ResourceRegistryDerivationData, TLC

SplitUpsertInterference == {<<"single-a", "duplicate">>}

SplitUpsertWitness ==
    [Derivation EXCEPT
        !.witnessCheckActMode = "stable",
        !.witnessInterferenceSteps = SplitUpsertInterference]

RejectsSplitUpsert == ~DerivationRecordAccepted(SplitUpsertWitness)

DerivationInit == progressState = "registry-rejection"
DerivationNext == UNCHANGED progressState
DerivationSpec == DerivationInit /\ [][DerivationNext]_progressVars

====
