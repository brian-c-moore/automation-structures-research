---- MODULE ALKClaimAuthoritySharedOwner_NEG ----
EXTENDS ALKClaimAuthorityControlBase

BadNext == Inject("shared-owner") \/ GoodNext

NegativeControlSpec == ControlInit /\ [][BadNext]_controlVars

NegativeControlExpected ==
    OwnershipControlHeld

====
