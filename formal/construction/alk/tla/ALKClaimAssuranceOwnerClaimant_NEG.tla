---- MODULE ALKClaimAssuranceOwnerClaimant_NEG ----
EXTENDS ALKClaimAssurancePerspectiveWitness
InjectOwnerClaimant ==
    /\ evidencePhase = "restored"
    /\ bindingFault = "none"
    /\ bindingFault' = "owner-as-claimant"
    /\ UNCHANGED evidenceVars
OwnerClaimantSpec == BindingInit /\ [][BindingNext \/ InjectOwnerClaimant]_bindingVars
====
