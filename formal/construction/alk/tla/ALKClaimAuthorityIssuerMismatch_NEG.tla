---- MODULE ALKClaimAuthorityIssuerMismatch_NEG ----
EXTENDS ALKClaimAuthorityControlBase

BadNext == Inject("issuer-mismatch") \/ GoodNext

NegativeControlSpec == ControlInit /\ [][BadNext]_controlVars

NegativeControlExpected ==
    IssuerControlHeld

====
