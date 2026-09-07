---- MODULE ALKClaimAssuranceSharedOwner_NEG ----
EXTENDS ALKClaimAssurancePerspectiveWitness
InjectSharedOwner ==
    /\ evidencePhase = "restored"
    /\ bindingFault = "none"
    /\ bindingFault' = "shared-owner"
    /\ UNCHANGED evidenceVars
SharedOwnerSpec == BindingInit /\ [][BindingNext \/ InjectSharedOwner]_bindingVars
====
