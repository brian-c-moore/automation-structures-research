---- MODULE ClaimRelativeOwnershipWitness_NonOwnerIssuer ----
EXTENDS ClaimRelativeOwnershipControlBase

BadSpec == ControlInit /\ [][GoodNext]_controlVars

====
