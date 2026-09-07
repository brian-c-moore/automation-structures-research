---- MODULE ClaimRelativeOwnershipWitness_AssuranceCredit ----
EXTENDS ClaimRelativeOwnershipControlBase

BadSpec == ControlInit /\ [][GoodNext]_controlVars

====
