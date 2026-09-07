---- MODULE ALKClaimAssuranceBindingWrongProducer_NEG ----
EXTENDS ALKClaimAssuranceBindingWitness
InjectBindingFault ==
    /\ evidencePhase = "restored"
    /\ bindingFault = "none"
    /\ bindingFault' = "wrong-producer"
    /\ UNCHANGED evidenceVars
BadBindingSpec == BindingInit /\ [][BindingNext \/ InjectBindingFault]_bindingVars
====
