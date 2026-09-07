---- MODULE ALKClaimAuthorityTCBPromotion_NEG ----
EXTENDS ALKClaimAuthorityControlBase

BadNext == Inject("tcb-promotion") \/ GoodNext

NegativeControlSpec == ControlInit /\ [][BadNext]_controlVars

NegativeControlExpected ==
    OwnershipControlHeld

====
