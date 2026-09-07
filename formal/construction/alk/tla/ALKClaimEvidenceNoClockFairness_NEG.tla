---- MODULE ALKClaimEvidenceNoClockFairness_NEG ----
EXTENDS ALKClaimEvidenceWitness

\* Finite tick-bound invariants cannot make an external clock advance.
UnfairEvidenceSpec == EvidenceInit /\ [][EvidenceNext]_evidenceVars
====
