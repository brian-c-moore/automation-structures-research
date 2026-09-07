---- MODULE ALKClaimReferenceBinding_Proof ----
EXTENDS ALKReferenceClaimAuthority, TLAPS

\* Parametric facts about the authorization conjunct used by the real gate.
\* The reference witness separately checks Next => CertifiedNext at every
\* reachable edge. These lemmas do not prove the reference state invariant.
THEOREM ReferenceAuthorizationRejectsWrongPrincipal ==
    ASSUME NEW profile, NEW revision, NEW action, NEW actor, NEW decision,
           actor # ReferenceProtocol(profile, revision)
    PROVE ~ReferenceAuthorization(profile, revision, action, actor, decision)
BY DEF ReferenceAuthorization, ReferenceController

THEOREM ReferenceAuthorizationRejectsIncompleteDecision ==
    ASSUME NEW profile, NEW revision, NEW action, NEW actor, NEW decision,
           decision # ReferenceMembers
    PROVE ~ReferenceAuthorization(profile, revision, action, actor, decision)
BY DEF ReferenceAuthorization

THEOREM ReferenceAuthorizationAdmitsDeclaredAction ==
    ASSUME NEW profile, NEW revision, NEW action,
           action \in ReferenceClaimActions
    PROVE ReferenceAuthorization(profile, revision, action,
              ReferenceProtocol(profile, revision), ReferenceMembers)
BY DEF ReferenceAuthorization, ReferenceController

THEOREM ReferenceAuthorizationHasOneController ==
    ASSUME NEW profile, NEW revision, NEW action, NEW actor, NEW other, NEW decision,
           ReferenceAuthorization(profile, revision, action, actor, decision),
           ReferenceAuthorization(profile, revision, action, other, decision)
    PROVE actor = other
BY DEF ReferenceAuthorization

====
