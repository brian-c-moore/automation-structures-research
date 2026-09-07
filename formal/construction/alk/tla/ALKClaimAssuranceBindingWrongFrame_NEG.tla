---- MODULE ALKClaimAssuranceBindingWrongFrame_NEG ----
EXTENDS ALKClaimAssuranceBindingWitness
InjectBindingFault ==
    /\ evidencePhase = "restored"
    /\ bindingFault = "none"
    /\ bindingFault' = "wrong-frame"
    /\ UNCHANGED evidenceVars
BadBindingSpec == BindingInit /\ [][BindingNext \/ InjectBindingFault]_bindingVars
====
