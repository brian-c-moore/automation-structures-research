---- MODULE ClaimRelativeOwnershipWitness_NEG_NonOwnerIssuer ----
EXTENDS ClaimRelativeOwnershipControlBase

BadNext == Inject("non-owner-issuer") \/ GoodNext

BadSpec == ControlInit /\ [][BadNext]_controlVars

====
