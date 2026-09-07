---- MODULE ClaimRelativeOwnershipWitness_NEG_WorkDelegationTransfers ----
EXTENDS ClaimRelativeOwnershipControlBase

BadNext == Inject("work-transfer") \/ GoodNext

BadSpec == ControlInit /\ [][BadNext]_controlVars

====
