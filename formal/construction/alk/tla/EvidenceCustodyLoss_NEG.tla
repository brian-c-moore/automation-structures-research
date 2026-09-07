---- MODULE EvidenceCustodyLoss_NEG ----
EXTENDS ALKSemanticModelWitness

EvidencePresent ==
    [state \in States |-> state = "committed-1"]

EvidencePersistent ==
    PersistentAcross(States, EvidencePresent, Actions["audit-loss"])

NegativeControlExpected == NegativeControlGate(EvidencePersistent)

====
