---- MODULE ALKClaimEvidenceWrongClaimant_NEG ----
EXTENDS ALKClaimEvidenceWitness

InjectBadClaim ==
    /\ evidencePhase = "captured"
    /\ recordClaimant' = "budget-worker"
    /\ UNCHANGED <<vars, evidenceLog, evidenceHash, evidencePhase, diagnosticTick, alarmRaised, stateRecovered, snapshotRetained, capturedBudget, recordFrame, recordSource, assertCurrentTruth, observeCurrentTruth>>
BadEvidenceSpec ==
    EvidenceInit /\ [][EvidenceNext \/ InjectBadClaim]_evidenceVars
====
