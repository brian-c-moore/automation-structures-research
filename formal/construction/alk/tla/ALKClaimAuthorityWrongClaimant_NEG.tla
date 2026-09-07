---- MODULE ALKClaimAuthorityWrongClaimant_NEG ----
EXTENDS ALKClaimAuthorityControlBase

BadNext == Inject("wrong-claimant") \/ GoodNext

NegativeControlSpec == ControlInit /\ [][BadNext]_controlVars

NegativeControlExpected ==
    ClaimantControlHeld

====
