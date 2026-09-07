---- MODULE ALKClaimEvidenceAssertionAsTruth_NEG ----
EXTENDS ALKClaimEvidenceWitness

InjectBadClaim ==
    /\ evidencePhase = "fault"
    /\ assertCurrentTruth' = TRUE
    /\ UNCHANGED <<vars, evidenceLog, evidenceHash, evidencePhase, diagnosticTick, alarmRaised, stateRecovered, snapshotRetained, capturedBudget, recordFrame, recordSource, recordClaimant, observeCurrentTruth>>
BadEvidenceSpec ==
    EvidenceInit /\ [][EvidenceNext \/ InjectBadClaim]_evidenceVars
====
