---- MODULE ClaimRelativeOwnershipWitness_NEG_SharedOwner ----
EXTENDS ClaimRelativeOwnershipControlBase

BadNext == Inject("shared-owner") \/ GoodNext

BadSpec == ControlInit /\ [][BadNext]_controlVars

====
