---- MODULE ALKClaimEvidenceLostCustody_NEG ----
EXTENDS ALKClaimEvidenceWitness

InjectBadClaim ==
    /\ evidencePhase = "captured"
    /\ snapshotRetained' = FALSE
    /\ UNCHANGED <<vars, evidenceLog, evidenceHash, evidencePhase, diagnosticTick, alarmRaised, stateRecovered, capturedBudget, recordFrame, recordSource, recordClaimant, assertCurrentTruth, observeCurrentTruth>>
BadEvidenceSpec ==
    EvidenceInit /\ [][EvidenceNext \/ InjectBadClaim]_evidenceVars
====
