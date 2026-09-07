---- MODULE ClaimRelativeOwnershipWitness_WorkDelegationTransfers ----
EXTENDS ClaimRelativeOwnershipControlBase

BadSpec == ControlInit /\ [][GoodNext]_controlVars

====
