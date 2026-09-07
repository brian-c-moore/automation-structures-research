---- MODULE ALKClaimRelationalIndependentChoice_NEG ----
EXTENDS ALKClaimRelationalWitness

IndependentComplete == Left!CompleteStep /\ Right!CompleteStep
BadPairSpec ==
    PairInit /\ [][PairBegin \/ IndependentComplete \/ PairDone]_pairVars
====
