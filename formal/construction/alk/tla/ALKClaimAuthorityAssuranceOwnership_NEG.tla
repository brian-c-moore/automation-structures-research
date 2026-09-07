---- MODULE ALKClaimAuthorityAssuranceOwnership_NEG ----
EXTENDS ALKClaimAuthorityControlBase

BadNext == Inject("assurance-ownership") \/ GoodNext

NegativeControlSpec == ControlInit /\ [][BadNext]_controlVars

NegativeControlExpected ==
    OwnershipControlHeld

====
