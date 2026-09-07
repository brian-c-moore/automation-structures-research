---- MODULE ALKClaimReferenceBindingWrongProfile_NEG ----
EXTENDS ALKClaimReferenceBindingWitness
InjectCertificateFault ==
    /\ certificateFault = "none"
    /\ configVersion = 1
    /\ certificateFault' = "wrong-profile"
    /\ UNCHANGED vars
BadCertificateSpec == CertificateInit /\ [][CertificateNext \/ InjectCertificateFault]_certificateVars
====
