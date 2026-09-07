---- MODULE ClaimEvidenceBinding ----
EXTENDS ClaimAssuranceProfiles

\* This interface consumes semantic proof premises supplied by its caller.
\* It does not establish the truth of evidence from a token or record field.
\* A concrete instance must evaluate EvidenceSemantics/GuaranteeSemantics
\* from its carrier, observations, or separately proved temporal contract.
BoundGuarantee(guarantee, Frames, Principals, Ownership, GuaranteeSemantics) ==
    /\ guarantee.frame \in OwnedFrames(Frames, Principals, Ownership)
    /\ guarantee.issuer = CanonicalOwner(guarantee.frame, Principals, Ownership)
    /\ guarantee.recipient = guarantee.frame.claimant
    /\ guarantee.predicate # ""
    /\ guarantee.relies # {}
    /\ guarantee.tcb # {}
    /\ guarantee.qualifiers \subseteq {"conditional"}
    /\ guarantee.outcome \in {"holds", "unavailable", "violated"}
    /\ guarantee.outcome = "holds"
    /\ GuaranteeSemantics[guarantee.id]

BoundEvidence(record, item, EvidenceSemantics) ==
    /\ item.frame = record.frame
    /\ item.proposition = record.proposition
    /\ item.source = record.source
    /\ item.verifier = record.verifier
    /\ item.claimant = record.claimant
    /\ item.observation = record.observation
    /\ item.custody \in {"retained", "current-observation"}
    /\ EvidenceSemantics[item.id]

BoundAssurance(record, Frames, Principals, Ownership,
               Evidence, EvidenceSemantics, Guarantees, GuaranteeSemantics) ==
    /\ record.frame \in Frames
    /\ record.claimant = record.frame.claimant
    /\ record.claimant \in Principals
    /\ ~(<<record.frame, record.claimant>> \in Ownership)
    /\ record.source \in Principals
    /\ record.verifier \in Principals
    /\ record.classes # {}
    /\ record.classes \subseteq AssuranceClassNames
    /\ record.proposition # ""
    /\ record.limits # {}
    /\ record.evidence \subseteq DOMAIN Evidence
    /\ record.mechanismClaims \subseteq DOMAIN Guarantees
    /\ \A id \in record.evidence :
          /\ BoundEvidence(record, Evidence[id], EvidenceSemantics)
          /\ Evidence[id].producer \in Principals
    /\ \A id \in record.mechanismClaims :
          /\ BoundGuarantee(Guarantees[id], Frames, Principals,
                            Ownership, GuaranteeSemantics)
          /\ Guarantees[id].frame = record.mechanismFrame
          /\ Guarantees[id].recipient = record.claimant
    /\ ("A0" \in record.classes =>
          "reliance-only" \in record.limits)
    /\ ("A1" \in record.classes =>
          /\ \E id \in record.evidence :
                /\ Evidence[id].kind = "attribution"
                /\ Evidence[id].producer = record.source
          /\ "assertion-not-truth" \in record.limits)
    /\ ("A2" \in record.classes =>
          /\ record.verifier # record.source
          /\ record.observation # "none"
          /\ \E id \in record.evidence :
                /\ Evidence[id].kind = "observation"
                /\ Evidence[id].producer = record.verifier
          /\ "point-observation" \in record.limits)
    /\ ("A3" \in record.classes =>
          /\ record.verifier # record.source
          /\ record.mechanismClaims # {}
          /\ \E id \in record.evidence :
                /\ Evidence[id].kind = "detection"
                /\ Evidence[id].producer = record.verifier
                /\ Evidence[id].coverage # {}
                /\ Evidence[id].elapsed <= record.detectionBound
          /\ "detection-not-prevention" \in record.limits)
    /\ ("A4" \in record.classes =>
          /\ record.mechanismClaims # {}
          /\ \E id \in record.evidence :
                /\ Evidence[id].kind = "restoration"
                /\ Evidence[id].elapsed <= record.recoveryTimeBound
                /\ Evidence[id].snapshotAge <= record.recoveryPointBound
          /\ "recovery-not-continuous-correctness" \in record.limits)
    /\ ("A5" \in record.classes =>
          /\ record.mechanismFrame = record.frame
          /\ record.mechanismClaims # {}
          /\ \A id \in record.mechanismClaims :
                Guarantees[id].issuer = record.source
          /\ "claimant-does-not-own" \in record.limits)

BoundClaimRecords(Frames, Principals, Ownership, Records,
                  Evidence, EvidenceSemantics, Guarantees, GuaranteeSemantics) ==
    /\ Ownership \subseteq Frames \X Principals
    /\ SingleOwnerPerFrame(Frames, Principals, Ownership)
    /\ DOMAIN EvidenceSemantics = DOMAIN Evidence
    /\ DOMAIN GuaranteeSemantics = DOMAIN Guarantees
    /\ \A id \in DOMAIN Guarantees :
          /\ Guarantees[id].id = id
          /\ BoundGuarantee(Guarantees[id], Frames, Principals,
                            Ownership, GuaranteeSemantics)
    /\ \A id \in DOMAIN Evidence : Evidence[id].id = id
    /\ \A id \in DOMAIN Records :
          /\ Records[id].id = id
          /\ BoundAssurance(Records[id], Frames, Principals, Ownership,
                            Evidence, EvidenceSemantics, Guarantees, GuaranteeSemantics)
====
