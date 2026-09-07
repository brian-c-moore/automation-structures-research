---- MODULE ALKClaimReferenceBindingWrongIssuer_NEG ----
EXTENDS ALKClaimReferenceBindingWitness
InjectCertificateFault ==
    /\ certificateFault = "none"
    /\ configVersion = 1
    /\ certificateFault' = "wrong-issuer"
    /\ UNCHANGED vars
BadCertificateSpec == CertificateInit /\ [][CertificateNext \/ InjectCertificateFault]_certificateVars
====
