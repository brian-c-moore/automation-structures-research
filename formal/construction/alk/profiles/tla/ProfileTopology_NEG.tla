---- MODULE ProfileTopology_NEG ----
EXTENDS ALKProfileConcreteInstances

AdjacentModularTopologyHeld ==
    ProfileTopologyBoundaryHeld("modular")

MutantCoLocatedComponentPlacement ==
    [component \in ProfileComponents |-> "module-a"]

MutantModularCoLocationHeld ==
    ProfileTopologyBoundaryTyped(
        "modular", ProfileActors,
        ProfileProcessBoundaries("modular"),
        ProfileProcessOwner("modular"),
        MutantCoLocatedComponentPlacement,
        ExpectedProfileCommitOwner("modular"))

NegativeControlExpected == NegativeControlGate(MutantModularCoLocationHeld)

====
