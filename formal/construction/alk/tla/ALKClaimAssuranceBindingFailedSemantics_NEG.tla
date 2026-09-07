---- MODULE ALKClaimAssuranceBindingFailedSemantics_NEG ----
EXTENDS ALKClaimAssuranceBindingWitness
InjectBindingFault ==
    /\ evidencePhase = "restored"
    /\ bindingFault = "none"
    /\ bindingFault' = "failed-semantics"
    /\ UNCHANGED evidenceVars
BadBindingSpec == BindingInit /\ [][BindingNext \/ InjectBindingFault]_bindingVars
====
