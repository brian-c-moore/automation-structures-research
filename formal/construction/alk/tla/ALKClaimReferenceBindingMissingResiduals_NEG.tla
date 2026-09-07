---- MODULE ALKClaimReferenceBindingMissingResiduals_NEG ----
EXTENDS ALKClaimReferenceBindingWitness
InjectCertificateFault ==
    /\ certificateFault = "none"
    /\ configVersion = 1
    /\ certificateFault' = "missing-residuals"
    /\ UNCHANGED vars
BadCertificateSpec == CertificateInit /\ [][CertificateNext \/ InjectCertificateFault]_certificateVars
====
