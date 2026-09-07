---- MODULE ALKClaimReferenceBindingWrongRevision_NEG ----
EXTENDS ALKClaimReferenceBindingWitness
InjectCertificateFault ==
    /\ certificateFault = "none"
    /\ configVersion = 1
    /\ certificateFault' = "wrong-revision"
    /\ UNCHANGED vars
BadCertificateSpec == CertificateInit /\ [][CertificateNext \/ InjectCertificateFault]_certificateVars
====
