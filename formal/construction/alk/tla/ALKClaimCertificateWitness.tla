---- MODULE ALKClaimCertificateWitness ----
EXTENDS ALKClaimAuthorityWitness

Certificate == INSTANCE ALKClaimCertificate

CatalogCertificateHeld ==
    /\ Certificate!CatalogInstanceCertificate.frames = Frames
    /\ Certificate!CatalogInstanceCertificate.schemas = SelectedSchemas
    /\ Certificate!CatalogInstanceCertificate.clauses = SelectedClauseOccurrences
    /\ Certificate!CatalogInstanceCertificate.decisive = AuthorityBoundaryBehaviorOfFrame
    /\ \A mode \in AuthorityModes :
          Certificate!CatalogInstanceCertificate.ownershipByMode[mode] = DerivedOwnership(mode)
    /\ ClaimAuthorityHeld
    /\ \A profile \in Certificate!CertificateProfileNames :
          \A mode \in Certificate!CertificateAssuranceModes :
            \A revision \in 1..2 :
              Certificate!StaticCertificateHeld(profile, mode, revision)
====
