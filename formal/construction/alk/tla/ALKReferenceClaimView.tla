---- MODULE ALKReferenceClaimView ----
EXTENDS ALKReferenceStateMachine

\* A read-only claim view over the operational state and a static certificate.
\* No proof graph or additional mutable claim state enters ALK-SPEC-1.
ClaimCertificate == INSTANCE ALKProfilesClaimCertificate

ConfiguredClaimCertificate ==
    ClaimCertificate!ProfileClaimCertificate(Profile, AssuranceMode, configVersion)

ReferenceClaimResults ==
    [claim \in ClaimCertificate!ReferenceClaimIds |->
        [ClaimCertificate!ReferenceStaticClaims(Profile, AssuranceMode, configVersion)[claim] EXCEPT
            !.outcome = IF MaxAttempts # 2 THEN "unavailable"
                         ELSE IF ReferencePredicateValues[claim] THEN "holds"
                         ELSE "violated"]]

ReferenceIssuedIds ==
    {claim \in ClaimCertificate!ReferenceClaimIds : ReferenceClaimResults[claim].outcome = "holds"}
ReferenceIssuedGuarantees ==
    [claim \in ReferenceIssuedIds |-> ReferenceClaimResults[claim]]
ReferenceAssuranceEvidence ==
    [claim \in ReferenceIssuedIds |->
        LET record == ReferenceClaimResults[claim]
        IN [id |-> claim, frame |-> record.frame, proposition |-> record.predicate,
            source |-> record.issuer, producer |-> record.issuer,
            verifier |-> record.recipient, claimant |-> record.recipient,
            observation |-> "current-reference-state", custody |-> "current-observation",
            kind |-> "model-predicate-evaluation"]]
ReferenceAssuranceRecords ==
    [claim \in ReferenceIssuedIds |->
        LET record == ReferenceClaimResults[claim]
        IN [id |-> claim, frame |-> record.frame, claimant |-> record.recipient,
            source |-> record.issuer, verifier |-> record.recipient, classes |-> {"A5"},
            proposition |-> record.predicate, evidence |-> {claim},
            observation |-> "current-reference-state",
            limits |-> {"claimant-does-not-own", "model-observation-not-deployment-evidence"},
            mechanismFrame |-> record.frame, mechanismClaims |-> {claim}]]
ReferenceAssuranceSemantics ==
    [claim \in ReferenceIssuedIds |-> MaxAttempts = 2 /\ ReferencePredicateValues[claim]]
ReferenceAssuranceBindingHeld ==
    ClaimCertificate!BoundClaimRecords(
        ClaimCertificate!ReferenceFrames(Profile, AssuranceMode, configVersion),
        ClaimCertificate!ReferencePrincipals(Profile, configVersion),
        ClaimCertificate!ReferenceOwnership(Profile, AssuranceMode, configVersion),
        ReferenceAssuranceRecords, ReferenceAssuranceEvidence, ReferenceAssuranceSemantics,
        ReferenceIssuedGuarantees, ReferenceAssuranceSemantics)

ReferenceResult ==
    [certificate |-> ConfiguredClaimCertificate,
     operation |-> operationId, phase |-> phase,
     claims |-> ReferenceClaimResults,
     assurances |-> ReferenceAssuranceRecords,
     evidence |-> ReferenceAssuranceEvidence,
     legacyCeiling |-> ClaimCertificate!LegacyCeilingComponents(configuredGuarantees),
     failureOutcome |-> lastFailure,
     residuals |-> ConfiguredClaimCertificate.residuals \cup
         (IF MaxAttempts = 2 THEN {} ELSE {"unverified-attempt-bound"})]

ReferenceCertificateBound ==
    /\ ReferenceCertificateKey =
         [version |-> ClaimCertificate!ClaimCertificateVersion,
          profile |-> Profile, assuranceMode |-> AssuranceMode, revision |-> configVersion]
    /\ ConfiguredClaimCertificate =
         ClaimCertificate!StaticClaimCertificate(Profile, AssuranceMode, configVersion)
    /\ ClaimCertificate!ProfileClaimCertificateHeld(Profile, AssuranceMode, configVersion)
    /\ ClaimCertificate!ProfileCatalogSelection(Profile) =
         ProfileWitness!ProfileSelectedStructures(Profile)
    /\ ClaimCertificate!ProfileExecutionSelection(Profile) =
         ProfileWitness!ProfileSelectedExecutionModality(Profile)
    /\ ClaimCertificate!ReferenceClaimActions = ActionNames \ {"init"}
    /\ ConfiguredClaimCertificate.revision = ownerRevision
    /\ ConfiguredClaimCertificate.revision = guaranteeRevision
    /\ ConfiguredClaimCertificate.revision = tcbRevision

ReferenceClaimResultsHeld ==
    \A claim \in ClaimCertificate!ReferenceClaimIds :
        /\ ReferenceClaimResults[claim].frame =
             ClaimCertificate!ReferenceClaimFrame(Profile, AssuranceMode, configVersion, claim)
        /\ ReferenceClaimResults[claim].issuer =
             ClaimCertificate!ReferenceProtocol(Profile, configVersion)
        /\ ReferenceClaimResults[claim].recipient = "reference-client"
        /\ ReferenceClaimResults[claim].qualifiers = {"conditional"}
        /\ ReferenceClaimResults[claim].outcome =
             IF MaxAttempts = 2 THEN "holds" ELSE "unavailable"

ReferenceClaimViewInvariant ==
    /\ SpecInvariant
    /\ ReferenceCertificateBound
    /\ ReferenceClaimResultsHeld
    /\ ReferenceAssuranceBindingHeld
====
