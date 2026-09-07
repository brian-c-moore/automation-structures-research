---- MODULE ALKClaimAuthorityWrongController_NEG ----
EXTENDS ALKClaimAuthorityControlBase

BadNext == Inject("wrong-controller") \/ GoodNext

NegativeControlSpec == ControlInit /\ [][BadNext]_controlVars

NegativeControlExpected ==
    OwnershipControlHeld

====
