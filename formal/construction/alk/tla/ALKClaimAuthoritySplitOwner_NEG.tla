---- MODULE ALKClaimAuthoritySplitOwner_NEG ----
EXTENDS ALKClaimAuthorityControlBase

BadNext == Inject("split-owner") \/ GoodNext

NegativeControlSpec == ControlInit /\ [][BadNext]_controlVars

NegativeControlExpected ==
    OwnershipControlHeld

====
