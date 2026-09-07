---- MODULE ClaimAssuranceProfiles ----
EXTENDS ClaimRelativeOwnership

AssuranceClassNames == {"A0", "A1", "A2", "A3", "A4", "A5"}

AssuranceProfilesTyped(
        Frames, Principals, Behaviors, EvidenceItems, Mechanisms,
        Guarantees, Ownership,
        GuaranteeFrame, GuaranteeIssuer, GuaranteeRecipient,
        Assurances, AssuranceFrame, AssuranceClaimant,
        AssuranceSource, AssuranceVerifier,
        AssuranceClassesOf, AssuranceEvidence,
        AttributedEvidence, IndependentEvidence,
        ObservationTimes, DetectionBound,
        DetectionCoverage, RecoveryMechanisms,
        RecoveryPointBound, RecoveryTimeBound,
        OwnerGuarantees) ==
    /\ AssuranceFrame \in [Assurances -> Frames]
    /\ AssuranceClaimant \in [Assurances -> Principals]
    /\ AssuranceSource \in [Assurances -> Principals]
    /\ AssuranceVerifier \in [Assurances -> Principals]
    /\ AssuranceClassesOf \in [Assurances -> SUBSET AssuranceClassNames]
    /\ AssuranceEvidence \in [Assurances -> SUBSET EvidenceItems]
    /\ AttributedEvidence \subseteq EvidenceItems
    /\ IndependentEvidence \subseteq EvidenceItems
    /\ ObservationTimes \in [Assurances -> STRING]
    /\ DetectionBound \in [Assurances -> Nat]
    /\ DetectionCoverage \in [Assurances -> SUBSET Behaviors]
    /\ RecoveryMechanisms \in [Assurances -> SUBSET Mechanisms]
    /\ RecoveryPointBound \in [Assurances -> Nat]
    /\ RecoveryTimeBound \in [Assurances -> Nat]
    /\ OwnerGuarantees \in [Assurances -> SUBSET Guarantees]
    /\ \A assurance \in Assurances :
          /\ AssuranceClassesOf[assurance] # {}
          /\ AssuranceClaimant[assurance]
               = AssuranceFrame[assurance].claimant
          /\ ("A1" \in AssuranceClassesOf[assurance]
                => AssuranceEvidence[assurance]
                     \cap AttributedEvidence # {})
          /\ ("A2" \in AssuranceClassesOf[assurance]
                => /\ AssuranceEvidence[assurance]
                       \cap IndependentEvidence # {}
                   /\ AssuranceVerifier[assurance]
                        # AssuranceSource[assurance]
                   /\ ObservationTimes[assurance] # "none")
          /\ ("A3" \in AssuranceClassesOf[assurance]
                => /\ AssuranceEvidence[assurance]
                       \cap IndependentEvidence # {}
                   /\ AssuranceVerifier[assurance]
                        # AssuranceSource[assurance]
                   /\ DetectionBound[assurance] > 0
                   /\ DetectionCoverage[assurance] # {})
          /\ ("A4" \in AssuranceClassesOf[assurance]
                => /\ RecoveryMechanisms[assurance] # {}
                   /\ RecoveryPointBound[assurance] > 0
                   /\ RecoveryTimeBound[assurance] > 0)
          /\ ("A5" \in AssuranceClassesOf[assurance]
                => LET frame == AssuranceFrame[assurance]
                       owner == CanonicalOwner(
                                    frame, Principals, Ownership)
                   IN /\ frame \in OwnedFrames(
                                      Frames, Principals, Ownership)
                      /\ AssuranceSource[assurance] = owner
                      /\ OwnerGuarantees[assurance] # {}
                      /\ \A guarantee \in OwnerGuarantees[assurance] :
                            /\ GuaranteeFrame[guarantee] = frame
                            /\ GuaranteeIssuer[guarantee] = owner
                            /\ GuaranteeRecipient[guarantee] =
                                 AssuranceClaimant[assurance])

NonOrdinalAssuranceProfile(assurance, AssuranceClassesOf) ==
    AssuranceClassesOf[assurance] \subseteq AssuranceClassNames

====
