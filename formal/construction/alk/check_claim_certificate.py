"""Source bindings for ALK-CLAIM-1; semantic truth belongs to named formal gates."""
from __future__ import annotations
import hashlib
import re
from pathlib import Path

SOURCES = {
    "binding": "formal/assurance/ownership/ClaimEvidenceBinding.tla",
    "instance": "formal/construction/alk/tla/ALKClaimInstantiationWitness.tla",
    "authority": "formal/construction/alk/tla/ALKClaimAuthorityBinding.tla",
    "assurance": "formal/construction/alk/tla/ALKClaimAssuranceBindingWitness.tla",
    "certificate": "formal/construction/alk/tla/ALKClaimCertificate.tla",
    "profile": "formal/construction/alk/profiles/tla/ALKProfilesClaimCertificate.tla",
    "reference": "formal/construction/alk/spec/tla/ALKReferenceStateMachine.tla",
    "view": "formal/construction/alk/tla/ALKReferenceClaimView.tla",
    "identity": "formal/construction/alk/tla/ALKReferenceClaimAuthority.tla",
}

REQUIRED = {
    "binding": ["record.claimant \\in Principals", "~(<<record.frame, record.claimant>> \\in Ownership)",
                "SingleOwnerPerFrame(Frames, Principals, Ownership)"],
    "instance": [
        "EXTENDS ALKClaimFrameData",
        "BudgetContract == INSTANCE Budget_Proof WITH",
        "SequentialContract == INSTANCE Sequential_Proof WITH",
    ],
    "authority": [
        "EXTENDS ALKClaimInstantiationWitness, ALKClaimAuthorityModel",
        "AuthorizationValid(mode, actor, decision, behavior)",
        "BoundBehaviorStep(behavior)",
    ],
    "assurance": [
        "BoundClaimRecords(BindingFrames, Principals, BindingOwnership,",
        "BindingEvidenceSemantics ==",
        'class = "A3" -> alarmRaised /\\ DetectionBoundHeld',
        "DiagnosticGate(label, actor, decision) ==",
    ],
    "certificate": [
        "ownershipByMode |-> [mode \\in AuthorityModes |-> DerivedOwnership(mode)]",
        "OwnersOf(record.frame, ReferencePrincipals(profile, revision),",
        '"no-catalog-to-profile-semantic-refinement"',
        '"no-implementation-or-deployment-conformance"',
        'qualifiers |-> {"conditional"}, outcome |-> "unassessed"',
    ],
    "profile": ["StaticClaimCertificate(profile, mode, revision)"],
    "identity": ['ClaimCertificateVersion == "ALK-CLAIM-1"'],
    "reference": [
        "Certificate == INSTANCE ALKReferenceClaimAuthority",
        "Spec == Init /\\ [][CertifiedNext]_vars",
        "Certificate!ReferenceAuthorization(Profile, configVersion, lastAction',",
        'claim = "reference-effect-count" -> NoDuplicateEffect',
        'claim = "reference-success-evidence" -> SuccessCoupled /\\ CommitEvidenceCoupled',
        "[] OTHER -> EffectOwnerCoupled",
        "profile |-> Profile, assuranceMode |-> AssuranceMode, revision |-> configVersion",
    ],
    "view": [
        "EXTENDS ALKReferenceStateMachine",
        "ClaimCertificate == INSTANCE ALKProfilesClaimCertificate",
        "ClaimCertificate!ProfileClaimCertificate(Profile, AssuranceMode, configVersion)",
        "MaxAttempts = 2 /\\ ReferencePredicateValues[claim]",
        "/\\ ReferenceAssuranceBindingHeld",
        "claims |-> ReferenceClaimResults",
        "assurances |-> ReferenceAssuranceRecords",
        "evidence |-> ReferenceAssuranceEvidence",
        "legacyCeiling |-> ClaimCertificate!LegacyCeilingComponents(configuredGuarantees)",
    ],
}


def normalized(source: str) -> str:
    # Reuse the entrypoint's string-aware, nested-comment-aware TLA lexer.
    from __main__ import strip_tla_comments
    return re.sub(r"\s+", "", strip_tla_comments(source))


def validate(sources: dict[str, str]) -> None:
    for key, needles in REQUIRED.items():
        code = normalized(sources[key])
        for needle in needles:
            if normalized(needle) not in code:
                raise ValueError(f"ALK claim source binding missing in {key}: {needle}")


def check_contract(primary: Path) -> str:
    sources = {key: (primary / path).read_text(encoding="utf-8") for key, path in SOURCES.items()}
    validate(sources)
    mutations = [
        ("binding", "~(<<record.frame, record.claimant>> \\in Ownership)", "TRUE"),
        ("binding", "SingleOwnerPerFrame(Frames, Principals, Ownership)", "TRUE"),
        ("reference", "Spec == Init /\\ [][CertifiedNext]_vars", "Spec == Init /\\ [][Next]_vars"),
        ("view", "/\\ ReferenceAssuranceBindingHeld", "/\\ TRUE"),
        ("view", "MaxAttempts = 2 /\\ ReferencePredicateValues[claim]", "TRUE"),
        ("reference", 'claim = "reference-effect-count" -> NoDuplicateEffect',
         'claim = "reference-effect-count" -> SuccessCoupled'),
        ("certificate", '"no-catalog-to-profile-semantic-refinement"', '"catalog-profile-certified"'),
    ]
    for key, old, new in mutations:
        if sources[key].count(old) != 1:
            raise ValueError(f"claim mutation does not have one exact site: {old}")
        changed = dict(sources)
        changed[key] = sources[key].replace(old, new)
        try:
            validate(changed)
        except ValueError:
            pass
        else:
            raise ValueError(f"claim source mutation escaped: {old}")
    digest = hashlib.sha256()
    for key in sorted(sources):
        digest.update(SOURCES[key].encode())
        digest.update(b"\0")
        digest.update(sources[key].encode())
        digest.update(b"\0")
    return f"ALK_CLAIM_CONTRACT|sources={len(sources)}|mutations={len(mutations)}|rejected={len(mutations)}|sha256={digest.hexdigest()}"
