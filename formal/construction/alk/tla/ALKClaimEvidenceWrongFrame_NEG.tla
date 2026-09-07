---- MODULE ALKClaimEvidenceWrongFrame_NEG ----
EXTENDS ALKClaimEvidenceWitness

InjectBadClaim ==
    /\ evidencePhase = "captured"
    /\ recordFrame' = SequentialFrame
    /\ UNCHANGED <<vars, evidenceLog, evidenceHash, evidencePhase, diagnosticTick, alarmRaised, stateRecovered, snapshotRetained, capturedBudget, recordSource, recordClaimant, assertCurrentTruth, observeCurrentTruth>>
BadEvidenceSpec ==
    EvidenceInit /\ [][EvidenceNext \/ InjectBadClaim]_evidenceVars
====
