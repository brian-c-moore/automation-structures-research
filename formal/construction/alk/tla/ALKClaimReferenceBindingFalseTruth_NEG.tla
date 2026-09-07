---- MODULE ALKClaimReferenceBindingFalseTruth_NEG ----
EXTENDS ALKClaimReferenceBindingWitness
ForgeEffectTruth ==
    /\ certificateFault = "none"
    /\ certificateFault' = "false-truth"
    /\ effectCount' = 2
    /\ UNCHANGED <<configVars, phase, operationId, requestDigest, presentedDigest,
                   requestEpoch, presentedEpoch, requestOrder, presentedOrder, attempts,
                   effectOwner, effectDurable, evidenceState, custodyState, recoveryIntent,
                   clientResponse, statusVars>>
BadCertificateSpec == CertificateInit /\ [][CertificateNext \/ ForgeEffectTruth]_certificateVars
====
