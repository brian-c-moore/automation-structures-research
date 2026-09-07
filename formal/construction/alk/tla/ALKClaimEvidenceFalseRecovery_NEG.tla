---- MODULE ALKClaimEvidenceFalseRecovery_NEG ----
EXTENDS ALKClaimEvidenceWitness
BadEvidenceSpec == EvidenceInit /\ [][Capture \/ InjectPersistentOverallocation \/ MonitorTick(TRUE) \/ RecoveryTick(FALSE) \/ EvidenceDone]_evidenceVars
====
