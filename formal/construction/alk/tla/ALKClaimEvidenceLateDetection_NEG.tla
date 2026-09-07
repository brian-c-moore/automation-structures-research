---- MODULE ALKClaimEvidenceLateDetection_NEG ----
EXTENDS ALKClaimEvidenceWitness
BadEvidenceSpec == EvidenceInit /\ [][Capture \/ InjectPersistentOverallocation \/ MonitorTick(FALSE) \/ RecoveryTick(TRUE) \/ EvidenceDone]_evidenceVars
====
