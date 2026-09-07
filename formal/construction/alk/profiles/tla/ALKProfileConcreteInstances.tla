---- MODULE ALKProfileConcreteInstances ----
EXTENDS ALKProfilesWitness

LOCAL LocalReference == INSTANCE ALKProfileTheoremInstances
    WITH Profile <- "local-reference"
LOCAL Modular == INSTANCE ALKProfileTheoremInstances
    WITH Profile <- "modular"
LOCAL Delegated == INSTANCE ALKProfileTheoremInstances
    WITH Profile <- "delegated"
LOCAL BoundedDistributed == INSTANCE ALKProfileTheoremInstances
    WITH Profile <- "bounded-distributed"

ExactConcreteProfileSubstitutionsHeld ==
    /\ LocalReference!InstantiatedProfileName = "local-reference"
    /\ Modular!InstantiatedProfileName = "modular"
    /\ Delegated!InstantiatedProfileName = "delegated"
    /\ BoundedDistributed!InstantiatedProfileName =
         "bounded-distributed"

AllProfileSpecificBoundariesHeld ==
    /\ ProfileSpecificBoundaryHeld("local-reference")
    /\ ProfileSpecificBoundaryHeld("modular")
    /\ ProfileSpecificBoundaryHeld("delegated")
    /\ ProfileSpecificBoundaryHeld("bounded-distributed")

AllProfileFailureLedgersHeld ==
    \A profile \in ProfileNames : ProfileExactFailureLedgerHeld(profile)

AllProfilesExactInstancesHeld ==
    /\ ExactProfileRegistryHeld
    /\ ExactConcreteProfileSubstitutionsHeld
    /\ AllProfilePremisesHeld
    /\ AllProfileConclusionsHeld
    /\ AllProfileSpecificBoundariesHeld
    /\ AllProfileFailureLedgersHeld

====
