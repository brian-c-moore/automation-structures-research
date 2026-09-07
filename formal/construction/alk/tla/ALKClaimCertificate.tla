---- MODULE ALKClaimCertificate ----
EXTENDS ALKClaimAuthorityModel, ClaimEvidenceBinding, ALKReferenceClaimAuthority

\* One static certificate definition. Catalog frames are the exact definitions
\* consumed by ALKClaimInstantiationWitness. Reference claims below are
\* separate ALK-SPEC-1 obligations, not aliases for those catalog predicates.
ReferenceClaimFrame(profile, mode, revision, claim) ==
    [subject |-> "ALK-SPEC-1/" \o profile,
     obligation |-> claim,
     mode |-> mode,
     scope |-> "one-operation-two-attempts/" \o
                  (IF revision = 1 THEN "revision-one" ELSE "revision-two"),
     observationBoundary |-> "complete-reference-effect-owner-phase-evidence-state",
     authorityBoundary |-> "closed-reference-transition-gate",
     claimant |-> "reference-client",
     failureModel |-> "only-declared-crash-partition-replay-and-custody-transitions",
     abstraction |-> "bounded-reference-state-machine",
     lifecyclePhase |-> "execution",
     propertyForm |-> "safety"]
ReferenceFrames(profile, mode, revision) ==
    {ReferenceClaimFrame(profile, mode, revision, claim) : claim \in ReferenceClaimIds}

\* Conservative coverage: the protocol admits every declared reference step.
\* This is control of the closed model transition, not authority over an
\* actual crash, network, external service, or deployed implementation.
ReferenceDecisiveOf(profile, mode, revision) ==
    [frame \in ReferenceFrames(profile, mode, revision) |-> ReferenceClaimActions]
ReferenceControlsOf(profile, mode, revision) ==
    [frame \in ReferenceFrames(profile, mode, revision) |->
        [principal \in ReferencePrincipals(profile, revision) |->
            {action \in ReferenceClaimActions :
                ReferenceController(profile, revision, action) = principal}]]
ReferenceExcludesOf(profile, mode, revision) ==
    [frame \in ReferenceFrames(profile, mode, revision) |->
        [principal \in ReferencePrincipals(profile, revision) |-> {}]]
ReferenceOwnership(profile, mode, revision) ==
    {pair \in ReferenceFrames(profile, mode, revision) \X ReferencePrincipals(profile, revision) :
        /\ pair[2] = ReferenceProtocol(profile, revision)
        /\ pair[2] \in EligibleOwners(pair[1], ReferencePrincipals(profile, revision),
            ReferenceDecisiveOf(profile, mode, revision),
            ReferenceControlsOf(profile, mode, revision),
            ReferenceExcludesOf(profile, mode, revision))}
ReferencePredicateName(claim) ==
    CASE claim = "reference-effect-count" -> "ALKReferenceStateMachine!NoDuplicateEffect"
      [] claim = "reference-success-evidence" ->
           "ALKReferenceStateMachine!SuccessCoupled /\\ CommitEvidenceCoupled"
      [] OTHER -> "ALKReferenceStateMachine!EffectOwnerCoupled"
ReferenceCertificateRelies ==
    {"exact-ALK-SPEC-1-transition-relation", "authentic-model-principal-labels",
     "atomic-reference-step", "one-operation-MaxAttempts-two",
     "no-unmodeled-writer-or-failure"}
ReferenceCertificateTCB ==
    {"reference-transition-gate", "reference-identity-and-configuration",
     "reference-effect-state", "reference-audit-and-recovery-state"}
ReferenceCertificateResiduals ==
    {"no-implementation-or-deployment-conformance",
     "no-arbitrary-failure-model",
     "no-catalog-to-profile-semantic-refinement",
     "no-wall-clock-or-eventual-recovery-claim",
     "no-minimal-TCB-result"}
CatalogInstanceCertificate ==
    [frames |-> Frames, schemas |-> SelectedSchemas,
     clauses |-> SelectedClauseOccurrences,
     decisive |-> AuthorityBoundaryBehaviorOfFrame,
     ownershipByMode |-> [mode \in AuthorityModes |-> DerivedOwnership(mode)],
     proofRoots |-> {"ALKClaimInstantiation_Proof", "ALKClaimAuthorityBinding_Proof"},
     controlRoots |-> {"ALKClaimActionBindingWitness", "ALKClaimAuthorityExecutionWitness"},
     ceiling |-> "capacity-two-steps-two-values-zero-or-one-no-crash-no-hidden-writer"]

ReferenceStaticClaims(profile, mode, revision) ==
    [claim \in ReferenceClaimIds |->
        LET frame == ReferenceClaimFrame(profile, mode, revision, claim)
            owner == ReferenceProtocol(profile, revision)
        IN [id |-> claim, frame |-> frame, issuer |-> owner,
            recipient |-> frame.claimant, accountable |-> owner,
            predicate |-> ReferencePredicateName(claim),
            evidence |-> {"ALK-SPEC-1-finite-models", "ALK-SPEC-1-seam-controls"},
            relies |-> ReferenceCertificateRelies, tcb |-> ReferenceCertificateTCB,
            qualifiers |-> {"conditional"}, outcome |-> "unassessed",
            assurance |-> [claimant |-> frame.claimant, source |-> owner,
                classes |-> {"A5"}, limit |-> "receiver-does-not-own-reference-obligation"],
            residuals |-> ReferenceCertificateResiduals]]
StaticClaimCertificate(profile, mode, revision) ==
    [version |-> ClaimCertificateVersion, profile |-> profile,
     assuranceMode |-> mode, revision |-> revision,
     catalogInstance |-> CatalogInstanceCertificate,
     referenceClaims |-> ReferenceStaticClaims(profile, mode, revision),
     ownership |-> ReferenceOwnership(profile, mode, revision),
     implementationConformance |-> "not-established",
     residuals |-> ReferenceCertificateResiduals]

StaticCertificateHeld(profile, mode, revision) ==
    /\ profile \in CertificateProfileNames
    /\ mode \in CertificateAssuranceModes
    /\ revision \in 1..2
    /\ CompleteOwnershipDisposition(ReferenceFrames(profile, mode, revision),
           ReferencePrincipals(profile, revision), ReferenceOwnership(profile, mode, revision),
           ReferenceDecisiveOf(profile, mode, revision), ReferenceControlsOf(profile, mode, revision),
           ReferenceExcludesOf(profile, mode, revision))
    /\ \A claim \in ReferenceClaimIds :
          LET record == ReferenceStaticClaims(profile, mode, revision)[claim]
          IN /\ record.frame.obligation = claim
             /\ record.issuer = record.accountable
             /\ OwnersOf(record.frame, ReferencePrincipals(profile, revision),
                    ReferenceOwnership(profile, mode, revision)) = {record.issuer}
             /\ record.recipient = record.frame.claimant
             /\ record.issuer # record.recipient
             /\ record.qualifiers = {"conditional"}
             /\ record.outcome = "unassessed"
             /\ record.tcb = ReferenceCertificateTCB
             /\ record.residuals = ReferenceCertificateResiduals

\* These projections preserve the historical compatibility outputs without
\* promoting a ceiling label to an issued or evidenced claim.
LegacyCeilingComponents(labels) ==
    [mechanismClasses |-> labels \cap {"prevention", "detection", "recovery"},
     qualifiers |-> labels \cap {"conditional"},
     outcomes |-> labels \cap {"lost"}]
====
