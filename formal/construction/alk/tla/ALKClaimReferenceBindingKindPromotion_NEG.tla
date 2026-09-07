---- MODULE ALKClaimReferenceBindingKindPromotion_NEG ----
EXTENDS ALKClaimReferenceBindingWitness
InjectCertificateFault ==
    /\ certificateFault = "none"
    /\ configVersion = 1
    /\ certificateFault' = "kind-as-obligation"
    /\ UNCHANGED vars
BadCertificateSpec == CertificateInit /\ [][CertificateNext \/ InjectCertificateFault]_certificateVars
====
