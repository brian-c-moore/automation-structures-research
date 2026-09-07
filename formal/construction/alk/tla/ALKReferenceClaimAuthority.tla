---- MODULE ALKReferenceClaimAuthority ----
EXTENDS Naturals, Sequences

\* Small operational certificate identity and authorization interface.
ClaimCertificateVersion == "ALK-CLAIM-1"
CertificateProfileNames == {"local-reference", "modular", "delegated", "bounded-distributed"}
CertificateAssuranceModes == {"at-commit", "precommit", "postcommit", "unavailable"}
ReferenceClaimIds == {"reference-effect-count", "reference-success-evidence", "reference-owner-binding"}
ReferenceClaimActions ==
    {"configure", "admit", "reject-unavailable", "prepare", "commit",
     "fail-before-effect", "apply-before-evidence", "recover", "lose-audit",
     "duplicate", "conflicting-duplicate", "lose-response", "retry-response",
     "stale-replay", "stale-read", "reject-reordered", "crash-before-check",
     "crash-between-check-and-commit", "crash-after-effect",
     "crash-before-evidence", "crash-after-commit", "restart", "partition",
     "heal-partition", "reject-partition", "external-owner-unavailable"}

ReferenceProtocol(profile, revision) ==
    profile \o (IF revision = 1 THEN "-reference-protocol-v1" ELSE "-reference-protocol-v2")
ReferenceMembers ==
    {"reference-identity", "reference-effect", "reference-audit",
     "reference-recovery", "reference-configuration"}
ReferencePrincipals(profile, revision) ==
    ReferenceMembers \cup {ReferenceProtocol(profile, revision), "reference-client"}

ReferenceController(profile, revision, action) == ReferenceProtocol(profile, revision)

ReferenceAuthorization(profile, revision, action, actor, decision) ==
    /\ action \in ReferenceClaimActions
    /\ actor = ReferenceController(profile, revision, action)
    /\ decision = ReferenceMembers

====
