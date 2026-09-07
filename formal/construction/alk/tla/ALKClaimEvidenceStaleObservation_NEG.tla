---- MODULE ALKClaimEvidenceStaleObservation_NEG ----
EXTENDS ALKClaimEvidenceWitness

InjectBadClaim ==
    /\ evidencePhase = "fault"
    /\ observeCurrentTruth' = TRUE
    /\ UNCHANGED <<vars, evidenceLog, evidenceHash, evidencePhase, diagnosticTick, alarmRaised, stateRecovered, snapshotRetained, capturedBudget, recordFrame, recordSource, recordClaimant, assertCurrentTruth>>
BadEvidenceSpec ==
    EvidenceInit /\ [][EvidenceNext \/ InjectBadClaim]_evidenceVars
====
