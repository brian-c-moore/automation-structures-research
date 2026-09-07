---- MODULE ClaimRelativeOwnershipWitness_NEG_AssuranceCredit ----
EXTENDS ClaimRelativeOwnershipControlBase

BadNext == Inject("assurance-credit") \/ GoodNext

BadSpec == ControlInit /\ [][BadNext]_controlVars

====
