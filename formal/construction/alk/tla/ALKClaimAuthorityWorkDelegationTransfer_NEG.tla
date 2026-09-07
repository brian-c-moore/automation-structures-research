---- MODULE ALKClaimAuthorityWorkDelegationTransfer_NEG ----
EXTENDS ALKClaimAuthorityControlBase

BadNext == Inject("work-transfer") \/ GoodNext

NegativeControlSpec == ControlInit /\ [][BadNext]_controlVars

NegativeControlExpected ==
    WorkDelegationControlHeld

====
