---- MODULE ALKProfilesClaimCertificate ----
EXTENDS ALKClaimCertificate

\* Static profile adapter. Keeping this outside the legacy theorem-interface
\* witness avoids cloning its entire namespace into every claim record.
ProfileClaimCertificate(profile, mode, revision) ==
    StaticClaimCertificate(profile, mode, revision)

ProfileClaimCertificateHeld(profile, mode, revision) ==
    /\ StaticCertificateHeld(profile, mode, revision)
    /\ (profile # "delegated" => mode = "at-commit")

ProfileCertificateResiduals == ReferenceCertificateResiduals

ProfileCatalogSelection(profile) ==
    IF profile = "bounded-distributed"
      THEN {"Budget", "ResourceRegistry", "ActuationPass", "AuditSink", "FederatedBudget"}
    ELSE {"Budget", "ResourceRegistry", "ActuationPass", "AuditSink"}
ProfileExecutionSelection(profile) ==
    CASE profile = "modular" -> "StepGraph"
      [] profile = "bounded-distributed" -> "ForkJoin"
      [] OTHER -> "Sequential"
====
