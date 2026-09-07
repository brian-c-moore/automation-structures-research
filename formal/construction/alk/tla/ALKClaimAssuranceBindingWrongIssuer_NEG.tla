---- MODULE ALKClaimAssuranceBindingWrongIssuer_NEG ----
EXTENDS ALKClaimAssuranceBindingWitness
InjectBindingFault ==
    /\ evidencePhase = "restored"
    /\ bindingFault = "none"
    /\ bindingFault' = "wrong-issuer"
    /\ UNCHANGED evidenceVars
BadBindingSpec == BindingInit /\ [][BindingNext \/ InjectBindingFault]_bindingVars
====
