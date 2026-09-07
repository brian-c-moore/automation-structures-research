---- MODULE ALKClaimEvidenceWrongSource_NEG ----
EXTENDS ALKClaimEvidenceWitness

InjectBadClaim ==
    /\ evidencePhase = "captured"
    /\ recordSource' = "budget-worker"
    /\ UNCHANGED <<vars, evidenceLog, evidenceHash, evidencePhase, diagnosticTick, alarmRaised, stateRecovered, snapshotRetained, capturedBudget, recordFrame, recordClaimant, assertCurrentTruth, observeCurrentTruth>>
BadEvidenceSpec ==
    EvidenceInit /\ [][EvidenceNext \/ InjectBadClaim]_evidenceVars
====
