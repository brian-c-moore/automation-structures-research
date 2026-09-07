---- MODULE ALKClaimAssuranceBindingWrongMechanismFrame_NEG ----
EXTENDS ALKClaimAssuranceBindingWitness
InjectBindingFault ==
    /\ evidencePhase = "restored"
    /\ bindingFault = "none"
    /\ bindingFault' = "wrong-mechanism-frame"
    /\ UNCHANGED evidenceVars
BadBindingSpec == BindingInit /\ [][BindingNext \/ InjectBindingFault]_bindingVars
====
