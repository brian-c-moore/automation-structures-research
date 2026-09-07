---- MODULE ClaimRelativeOwnershipWitness_SharedOwner ----
EXTENDS ClaimRelativeOwnershipControlBase

BadSpec == ControlInit /\ [][GoodNext]_controlVars

====
