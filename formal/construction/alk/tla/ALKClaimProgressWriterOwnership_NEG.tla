---- MODULE ALKClaimProgressWriterOwnership_NEG ----
EXTENDS ALKClaimProgressWitness

PromoteWriter ==
    /\ progressControl = "none"
    /\ progressControl' = "writer-as-owner"
    /\ UNCHANGED vars
BadProgressSpec ==
    ProgressInit /\ [][ProgressNext \/ PromoteWriter]_progressVars
====
